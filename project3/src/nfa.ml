open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)
let rec move_helper delta q s =
  match delta with
  | [] -> []
  | h::t -> match h with 
    |(start, transition, finish) -> if (start = q && transition = s) then
      insert_all [finish] (move_helper t q s)
    else move_helper t q s;; 

let rec move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  match qs with
  | [] -> []
  | h::t -> insert_all (move_helper nfa.delta h s) (move nfa t s);;

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  let rec rec_step qs lst= 
    match qs with 
    | [] -> []
    | h::t -> if (elem h lst) = false then 
      let epsilon = move_helper nfa.delta h None in 
        union [h] (rec_step (union t epsilon) (union lst [h]))
    else rec_step t lst in
  rec_step qs [];;

let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let rec rec_step loc input = 
    match input with 
    | [] -> if not((intersection (e_closure nfa loc) nfa.fs) = []) then true else false
    | h::t -> rec_step (move nfa (e_closure nfa loc) (Some h)) t in
  rec_step ([nfa.q0]) (explode s);;

(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.fold_left (fun acc c -> union [e_closure nfa (move nfa qs (Some c))] acc) [] nfa.sigma;;

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list =
  List.fold_left (fun acc c -> union [(qs, Some c, e_closure nfa (move nfa qs (Some c)))] acc) [] nfa.sigma;;

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  let rec rec_step lst =
    match lst with 
    |[] -> false
    |h::t -> if (elem h qs) = true then true else rec_step t in 
  if rec_step nfa.fs then [qs] else [];;

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t) (work: 'q list list) : ('q list, 's) nfa_t =
    let nfa_to_dfa_helper nfa dfa lst = 
    let hq0 = e_closure nfa [nfa.q0] in
    let hfs = new_finals nfa lst in
    let ndelta = new_trans nfa lst in
    {sigma = nfa.sigma; qs = union dfa.qs [lst];  q0 = hq0; fs = union dfa.fs hfs; delta = union dfa.delta ndelta;} in 
    match work with
    |[]-> {sigma= nfa.sigma; qs= []; q0= []; fs= []; delta= [];}
    |h::t -> 
    let lst2 = new_states nfa h in
    fold_left (fun acc x-> 
    let h_dfa = nfa_to_dfa_helper nfa acc h in
    if (elem (e_closure nfa x) dfa.qs)  
    then h_dfa else nfa_to_dfa_step nfa h_dfa [e_closure nfa x]) dfa lst2;; 

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t =
  nfa_to_dfa_step nfa ({sigma= nfa.sigma; qs= []; q0= []; fs= []; delta= [];}) [e_closure nfa [nfa.q0]];;