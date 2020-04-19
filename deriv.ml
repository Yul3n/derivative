exception Error of string

let last l =
  match l with
    _ :: lst :: [] -> lst
  | lst :: []      -> lst
  | _              -> raise (Invalid_argument
                               "Can't determine the last element of an empty list.")

let rec firsts l =
  match l with
    []
  | _ :: []  -> []
  | hd :: tl -> hd :: firsts tl

type token
  = PLUS
  | MINUS
  | TIMES
  | POWER
  | DIV
  | LPAR
  | RPAR
  | NUM of int
  | VAR of string

let rec lexer str pos =
  let is_digit chr = (Char.code('0') <= Char.code chr) &&
                     (Char.code('9') >= Char.code chr)
  in
  let is_alpha chr = (Char.code('A') <= Char.code chr) &&
                     (Char.code('Z') >= Char.code chr) ||
                     (Char.code('a') <= Char.code chr) &&
                     (Char.code('z') >= Char.code chr)
  in
  let rec parse_f f str pos =
    match pos with
      len when len = String.length str -> ""
    | _ -> match String.get str pos with
        chr when f chr -> (String.make 1 chr) ^ parse_f f str (pos + 1)
      | _ -> ""
  in
  match String.get str pos with
    '+' -> PLUS,  pos + 1
  | '-' -> MINUS, pos + 1
  | '*' -> TIMES, pos + 1
  | '/' -> DIV,   pos + 1
  | '^' -> POWER, pos + 1
  | '(' -> LPAR,  pos + 1
  | ')' -> RPAR,  pos + 1
  | n when is_digit n ->
    let num = parse_f is_digit str pos in
    let len = String.length num        in
    NUM (int_of_string num), pos + len
  | a when is_alpha a ->
    let var = parse_f is_alpha str pos in
    let len = String.length var        in
    VAR var, pos + len
  | ' ' | '\t' | '\n' -> lexer str (pos + 1)
  | c -> raise (Error ("Unexpected character: " ^ (String.make 1 c) ^
                       ", at position: " ^ (string_of_int pos)))

type op
  = Plus
  | Mult
  | Pow
  | Minus
  | Div

type expr
  = Var of string
  | App of string * expr
  | BinOp of expr * op * expr
  | Const of int

let rec reduce e =
  match e with
    [] -> raise (Error "empty expression")
  | e :: [] -> e
  | f :: s :: tl -> reduce (BinOp (f, Mult, s) :: tl)
                     
let rec parser ?(is_math=false) tokens exprs =
  let rec parse_mul tokens lval =
    let nval, ntl =
      match tokens with
        TIMES :: tl  -> let rval, tl = parser tl [] ~is_math:true in
        BinOp (lval, Mult, (reduce rval)), tl
      | DIV :: tl -> let rval, tl = parser tl [] ~is_math:true in
        BinOp (lval, Div, (reduce rval)), tl
      | tl           -> lval, tl
    in
    match ntl with
      TIMES :: _ | DIV :: _ -> parse_mul ntl nval
    | _                     -> nval, ntl
  in
  let rec parse_add tokens lval =
    let nval, ntl =
      match tokens with
        PLUS :: tl  -> let rmul, tl = parser tl [] ~is_math:true in
        let rval, tl = parse_mul tl (reduce rmul) in
        BinOp (lval, Plus, rval), tl
      | MINUS :: tl -> let rmul, tl = parser tl [] ~is_math:true in
        let rval, tl = parse_mul tl (reduce rmul) in
        BinOp (lval, Plus, (BinOp(rval, Mult, Const(-1)))), tl
      | tl           -> lval, tl
    in
    match ntl with
      PLUS :: _ | MINUS :: _ -> parse_add ntl nval
    | _                      -> nval, ntl
  in
  let rec parse_par tokens =
    let e, tl = parser tokens [] in
    match tl with
      RPAR :: tl -> [reduce e], tl
    | [] -> raise (Error "Unclosed parenthesis")
    | _ -> let t, tl = parse_par tl in
      (reduce e) :: t, tl
  in
  let e, tl =
    match tokens with
      NUM n :: tl -> exprs @ [Const n], tl
    | VAR v :: LPAR :: tl ->
      let e, tl = parse_par tl in
      let b = App(v, reduce e) in
      exprs @ [b], tl
    | VAR v :: tl -> exprs @ [Var v], tl
    | LPAR :: tl ->
      let e, tl = parse_par tl in
      exprs @ [reduce e], tl
    | TIMES :: tl
    | DIV   :: tl -> let e, tl = parse_mul tokens (last exprs) in
      (firsts exprs) @ [e], tl
    | MINUS :: tl
    | PLUS  :: tl -> let e, tl = parse_add tokens (last exprs) in
      (firsts exprs) @ [e], tl
    | _ -> raise (Invalid_argument "")
  in
  match is_math with
    false ->
    begin
      match tl with
        []
      | RPAR :: _ -> e, tl
      | POWER :: tl -> let ex, tl = parser ~is_math:true tl [] in
        parser tl (firsts e @ [BinOp(last e, Pow, reduce ex)])
      | _ -> parser tl e
    end
  | true ->
    match tl with
      POWER :: tl -> let ex, tl = parser ~is_math:true tl [] in
      firsts e @ [BinOp(last e, Pow, reduce ex)], tl
    | _ -> e, tl

let rec is_const e v =
  match e with
    Const _ -> true
  | Var x when x = v -> false
  | Var _ -> true
  | App(_, x) -> is_const x v
  | BinOp(l, _, r) -> (is_const l v) && (is_const r v)

let rec derivate e v =
  match e with
    e when is_const e v -> Const 0
  | Var x when x = v -> Const 1
  | BinOp (f, Pow, e) ->
    let f' = derivate f v in
    BinOp (BinOp (e, Mult, BinOp(f, Pow, BinOp(e, Minus, Const 1))), Mult, f')
  | BinOp (f, Mult, g) ->
    let f' = derivate f v in
    let g' = derivate g v in
    BinOp (BinOp(g, Mult, f'), Plus, BinOp(g', Mult, f))
  | BinOp (f, Div, g) ->
    let f' = derivate f v in
    let g' = derivate g v in
    BinOp (BinOp (BinOp(g, Mult, f'), Minus, BinOp(g', Mult, f)),
           Div, BinOp(g, Pow, Const 2))
  | BinOp (f, Plus, g) ->
    let f' = derivate f v in
    let g' = derivate g v in
    BinOp (f', Plus, g')
  | App (f, x) ->
    let get_der f x =
      match f with
        "sin" -> App("cos", x)
      | "cos" -> BinOp (Const (-1), Mult, App("sin", x))
      | "exp" -> App("exp", x)
      | "log" -> BinOp(Const 1, Div, x)
      | _ -> raise Not_found
    in
    let f'g = get_der f x  in
    let g'  = derivate x v in
    BinOp(f'g, Mult, g')
  | _ -> raise Not_found

let rec free_vars e =
  match e with
    Const _ -> []
  | Var v when not (List.mem v ["sin"; "cos"; "exp"; "log"]) -> [v]
  | Var _ -> []
  | App (_, x) -> free_vars x
  | BinOp (g, _, d) -> (free_vars g) @ (free_vars d)

let rec simplify e =
  match e with
    BinOp (e, Plus, Const 0)
  | BinOp (Const 0, Plus, e)
  | BinOp (e, Minus, Const 0)
  | BinOp (e, Mult, Const 1)
  | BinOp (e, Div, Const 1)
  | BinOp (Const 1, Mult, e)
  | App ("exp", App("log", e))
  | BinOp (e, Pow, Const 1) -> simplify e
  | BinOp (_, Pow, Const 0)
  | BinOp (Const 1, Pow, _) -> Const 1
  | BinOp (_, Mult, Const 0)
  | BinOp (Const 0, Mult, _) -> Const 0
  | BinOp (Const 0, Minus, e) -> simplify (BinOp (Const (-1), Mult, e))
  | Const n -> Const n
  | Var v   -> Var v
  | App (f, x) -> App (f, simplify x)
  | BinOp (Const n, Plus, Const m) -> Const (n + m)
  | BinOp (Const n, Minus, Const m) -> Const (n - m)
  | BinOp (Const n, Mult, Const m) -> Const (n * m)
  | BinOp (Const n, Div, Const m) -> Const (n / m)
  | BinOp (BinOp (Const n, Mult, x), Plus, (BinOp(Const m, Mult, y))) when x = y ->
    BinOp (Const (n + m), Mult, simplify x)
  | BinOp (BinOp (Const n, Mult, x), Minus, (BinOp(Const m, Mult, y))) when x = y ->
    BinOp (Const (n - m), Mult, simplify x)
  | BinOp (g, Mult, BinOp(n, Div, d)) when g = d -> simplify n
  | BinOp (BinOp(n, Div, g), Mult, d) when g = d -> simplify n
  | BinOp (g, o, d) ->
    let g' = simplify g in
    let d' = simplify d in
    (* Check if the terms are unsimplifialble to avoid an infinite loop. *)
    if (g <> g') || (d <> d')
    then simplify (BinOp (g', o, d'))
    else BinOp(g', o, d')

let rec pprint e =
  match e with
    Const n -> string_of_int n
  | Var v   -> v
  | App (f, x) -> f ^ "(" ^ (pprint x) ^ ")"
  | BinOp (g, Plus, d) -> (pprint g) ^ " + " ^ (pprint d)
  | BinOp (g, Minus, d) -> (pprint g) ^ " - " ^ (pprint d)
  | BinOp (g, Mult, d) -> "(" ^ (pprint g) ^ ") * (" ^ (pprint d) ^ ")"
  | BinOp (g, Div, d) -> "(" ^ (pprint g) ^ ") / (" ^ (pprint d) ^ ")"
  | BinOp (g, Pow, d) -> "(" ^ (pprint g) ^ ") ^ (" ^ (pprint d) ^ ")"

let rec repl () =
  print_string "> ";
  let s   = read_line () in
  let len = String.length s in
  let rec lex p =
    let t, p = lexer s p in
    match p with
      l when l = len -> [t]
    | p -> t :: lex p
  in
  let tokens = lex 0 in
  let e = parser tokens [] in
  let p = reduce (fst e) in
  List.iter
    (fun x -> print_endline ("df/d" ^ x ^ ": " ^ (pprint (simplify (derivate p x)))))
    (List.sort_uniq compare (free_vars p));
  repl()

let _ = repl()
