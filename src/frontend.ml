module T = Ast.T
open Ocaml_parser
open Parsetree
open Sugar

let layout_ t =
  let _ = Format.flush_str_formatter () in
  Pprintast.core_type Format.str_formatter t;
  Format.flush_str_formatter ()

let desc_to_ct t =
  {
    ptyp_desc = t;
    ptyp_loc = Location.none;
    ptyp_loc_stack = [];
    ptyp_attributes = [];
  }

let rec core_type_to_t ct = core_type_desc_to_t ct.ptyp_desc

and core_type_desc_to_t t =
  match t with
  | Ptyp_any | Ptyp_object (_, _) -> failwith "type object"
  | Ptyp_class (_, _)
  | Ptyp_alias (_, _)
  | Ptyp_variant (_, _, _)
  | Ptyp_package _ | Ptyp_extension _ ->
      _failatwith __FILE__ __LINE__ "die"
  | Ptyp_poly (_, _) -> _failatwith __FILE__ __LINE__ "unimp: poly"
  | Ptyp_var name ->
      (* let () = Printf.printf "parsing type var: %s\n" name in *)
      T.Ty_var name
  | Ptyp_arrow (_, t1, t2) -> T.Ty_arrow (core_type_to_t t1, core_type_to_t t2)
  | Ptyp_tuple ts -> T.Ty_tuple (List.map core_type_to_t ts)
  | Ptyp_constr (lc, ts) -> (
      match (Longident.flatten lc.txt, ts) with
      | [ "unit" ], [] -> T.Ty_unit
      | [ "bool" ], [] -> T.Ty_bool
      | [ "int" ], [] -> T.Ty_int
      (* | [ "ref" ], [ t ] -> T.Ref (core_type_to_t t) *)
      | [ "list" ], [ t ] -> T.Ty_list (core_type_to_t t)
      (* | [ "array" ], [ t ] -> T.Array (core_type_to_t t) *)
      (* HACK: here, assume we know the name of abstact type name *)
      (* | [ "t" ], [] -> T.Uninterp "t" *)
      (* | [ a; "t" ], [] -> T.Uninterp Sugar.(spf "%s.t" a) *)
      | [ c ], args -> T.Ty_constructor (c, List.map core_type_to_t args)
      | _, _ -> failwith @@ Printf.sprintf "un-imp: %s" (layout_ @@ desc_to_ct t)
      )

let core_type_to_notated_t ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> (Some name.txt, core_type_to_t ty)
  | _ -> (None, core_type_to_t ct)

let rec t_to_core_type t = desc_to_ct (t_to_core_type_desc t)

and t_to_core_type_desc t =
  let open Longident in
  let open Location in
  let mk0 name = Ptyp_constr (mknoloc @@ Lident name, []) in
  let mk1 name t = Ptyp_constr (mknoloc @@ Lident name, [ t ]) in
  let aux = function
    | T.Ty_unknown -> mk0 "unknown"
    | T.Ty_var name ->
        let res = Ptyp_var name in
        (* let () = *)
        (*   Printf.printf "output res: %s\n" @@ layout_ @@ desc_to_ct res *)
        (* in *)
        res
    | T.Ty_unit -> mk0 "unit"
    | T.Ty_bool -> mk0 "bool"
    | T.Ty_int -> mk0 "int"
    | T.Ty_list t -> mk1 "list" (t_to_core_type t)
    | T.Ty_tree t -> mk1 "tree" (t_to_core_type t)
    | T.Ty_tuple t -> Ptyp_tuple (List.map t_to_core_type t)
    | T.Ty_arrow (t1, t2) ->
        Ptyp_arrow (Asttypes.Nolabel, t_to_core_type t1, t_to_core_type t2)
    | Ty_constructor (id, args) ->
        Ptyp_constr
          ( (Location.mknoloc
            @@
            match Longident.unflatten [ id ] with
            | None -> _failatwith __FILE__ __LINE__ "die"
            | Some x -> x),
            List.map t_to_core_type args )
  in
  aux t

let notated_t_to_core_type (name, t) =
  let ct = t_to_core_type t in
  match name with
  | None -> ct
  | Some name -> desc_to_ct (Ptyp_extension (Location.mknoloc name, PTyp ct))

let layout t = layout_ (t_to_core_type t)
let of_string str = core_type_to_t @@ Parse.core_type @@ Lexing.from_string str
let layout_l ts = Zzdatatype.Datatype.List.split_by_comma layout ts

open Zzdatatype.Datatype

let _type_unify_ file line m t1 t2 =
  let open T in
  (* let () = Printf.printf "unify %s --> %s\n" (layout t1) (layout t2) in *)
  let rec unify m (t1, t2) =
    match (t1, t2) with
    | Ty_unknown, _ -> (m, t2)
    | _, Ty_unknown -> (m, t2)
    | Ty_var n, t2 -> (
        match StrMap.find_opt m n with
        | Some t1 ->
            let t = _check_equality file line eq t1 t2 in
            (m, t)
        | None ->
            let m = StrMap.add n t2 m in
            (m, t2))
    | Ty_list t1, Ty_list t2 ->
        let m, t = unify m (t1, t2) in
        (m, Ty_list t)
    | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) ->
        let id = _check_equality file line String.equal id1 id2 in
        (* let () = *)
        (*   Printf.printf "(%s) v.s. (%s)\n" *)
        (*     (List.split_by_comma layout ts1) *)
        (*     (List.split_by_comma layout ts2) *)
        (* in *)
        let m, ts =
          List.fold_left
            (fun (m, ts) (t1, t2) ->
              let m, t = unify m (t1, t2) in
              (m, ts @ [ t ]))
            (m, []) (List.combine ts1 ts2)
        in
        (m, Ty_constructor (id, ts))
    | Ty_tree _, _ ->
        _failatwith file line "built-in tree type, should not happen"
    | Ty_arrow (t11, t12), Ty_arrow (t21, t22) ->
        let m, t1 = unify m (t11, t21) in
        let m, t2 = unify m (t12, t22) in
        (m, Ty_arrow (t1, t2))
    | Ty_tuple ts1, Ty_tuple ts2 when List.length ts1 == List.length ts2 ->
        let m, ts =
          List.fold_left
            (fun (m, ts) (t1, t2) ->
              let m, t = unify m (t1, t2) in
              (m, ts @ [ t ]))
            (m, []) (List.combine ts1 ts2)
        in
        (m, Ty_tuple ts)
    | _, Ty_var _ ->
        (m, t1)
        (* _failatwith file line "argment should not contain type var" *)
    | _, _ -> (
        ( m,
          try _check_equality file line eq t1 t2
          with e ->
            Printf.printf "%s != %s\n" (layout t1) (layout t2);
            raise e ))
  in
  unify m (t1, t2)

let _type_unify file line t1 t2 =
  snd @@ _type_unify_ file line StrMap.empty t1 t2
