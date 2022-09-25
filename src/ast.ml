module Q = Nt.Q
module Smtty = Nt.Smtty

module T = struct
  include Frontend
  include Nt.T
  open Zzdatatype.Datatype
  open Sugar

  let subst t (id, ty) =
    let rec aux t =
      match t with
      | Ty_unknown | Ty_unit | Ty_int | Ty_bool -> t
      | Ty_var x -> if String.equal x id then ty else t
      | Ty_list x -> Ty_list (aux x)
      | Ty_tree x -> Ty_tree (aux x)
      | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
      | Ty_tuple xs -> Ty_tuple (List.map aux xs)
      | Ty_constructor (id, args) -> Ty_constructor (id, List.map aux args)
    in
    aux t

  let subst_m m t = StrMap.fold (fun id ty t -> subst t (id, ty)) m t

  let _type_unify_ file line m t1 t2 =
    let open T in
    (* let () = Printf.printf "unify %s --> %s\n" (layout t1) (layout t2) in *)
    let rec unify m (t1, t2) =
      let t1 = subst_m m t1 in
      (* let () = Printf.printf "one %s --> %s\n" (layout t1) (layout t2) in *)
      match (t1, t2) with
      | Ty_unknown, _ -> (m, t2)
      | Ty_var n, t2 -> (
          match StrMap.find_opt m n with
          | Some _ -> _failatwith __FILE__ __LINE__ ""
          | None ->
              let m = StrMap.add n t2 m in
              (m, t2))
      | Ty_list t1, Ty_list t2 ->
          let m, t = unify m (t1, t2) in
          (m, Ty_list t)
      | Ty_tree t1, Ty_tree t2 ->
          let m, t = unify m (t1, t2) in
          (m, Ty_tree t)
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
      | _, Ty_unknown -> (m, t1)
      | _, Ty_var _ ->
          (* (m, t1) *)
          _failatwith file line "argment should not contain type var"
      | _, _ -> (
          ( m,
            try _check_equality file line eq t1 t2
            with e ->
              Printf.printf "%s != %s\n" (layout t1) (layout t2);
              raise e ))
    in
    try unify m (t1, t2)
    with e ->
      Printf.printf "Type unify error: %s ==> %s\n" (layout t1) (layout t2);
      raise e

  let _type_unify file line t1 t2 =
    snd @@ _type_unify_ file line StrMap.empty t1 t2
end

module NotatedT = struct
  open Sexplib.Std

  type t = string option * T.t [@@deriving sexp]

  let eq (a1, b1) (a2, b2) =
    match (a1, a2) with
    | None, None -> T.eq b1 b2
    | Some a1, Some a2 when String.equal a1 a2 -> T.eq b1 b2
    | _ -> false
end

module NT = T

module SMTtyped = struct
  include Smtty

  type 'a typed = { x : 'a; ty : t } [@@deriving sexp]

  let map (f : 'a -> 'b) { x; ty } = { x = f x; ty }
  let typed_eq a b = String.equal a.x b.x && eq a.ty b.ty
end

module Ntyped = struct
  include NT

  type 'a typed = { x : 'a; ty : t } [@@deriving sexp]

  let map (f : 'a -> 'b) { x; ty } = { x = f x; ty }
  let typed_eq a b = String.equal a.x b.x && eq a.ty b.ty
  let to_smttyped { x; ty } = SMTtyped.{ x; ty = to_smtty ty }
end

module NNtyped = struct
  include NotatedT

  type 'a typed = { x : 'a; ty : t } [@@deriving sexp]

  let map (f : 'a -> 'b) { x; ty } = { x = f x; ty }
  let typed_eq a b = String.equal a.x b.x && eq a.ty b.ty
  let to_ntyped { x; ty } = Ntyped.{ x; ty = snd ty }
end
