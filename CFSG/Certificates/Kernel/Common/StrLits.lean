module

public meta import Lean
public import Lean.Exception

public section

namespace CFSG.KC.StrLits

theorem leaf_tail (s : String) (ls R : List Char) (h : String.ofList ls = s) :
    String.ofList (List.append ls R) = s ++ String.ofList R := by
  rw [← h]; exact String.ofList_append

theorem leaf_end (s : String) (ls : List Char) (h : String.ofList ls = s) :
    String.ofList ls = s := h

theorem node_tail {a b : String} {La Lb R : List Char}
    (ha : String.ofList La = a ++ String.ofList Lb) (hb : String.ofList Lb = b ++ String.ofList R) :
    String.ofList La = a ++ b ++ String.ofList R := by
  rw [ha, hb, String.append_assoc]

theorem node_end {a b : String} {La Lb : List Char}
    (ha : String.ofList La = a ++ String.ofList Lb) (hb : String.ofList Lb = b) :
    String.ofList La = a ++ b := by
  rw [ha, hb]

theorem of_ofList {p : String → Prop} {c : String} {L : List Char} (h : String.ofList L = c)
    (hp : p (String.ofList L)) : p c :=
  h ▸ hp

open Lean Meta Elab Tactic

meta def charsE (s : String) : Expr :=
  s.toList.foldr
    (fun c l => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char)
      (mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat)) l)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Char))

meta def appendArgs? (t : Expr) : Option (Expr × Expr) :=
  if t.isAppOfArity ``HAppend.hAppend 6 then some (t.getArg! 4, t.getArg! 5)
  else if t.isAppOfArity ``String.append 2 then some (t.getArg! 0, t.getArg! 1)
  else none

meta partial def build (t : Expr) (tail : Option Expr) : MetaM (Expr × Expr) := do
  let t := t.consumeMData
  match t, tail with
  | .lit (.strVal s), some R =>
    let ls := charsE s
    let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``String) (mkApp (mkConst ``String.ofList) ls)
    return (mkApp3 (mkConst ``List.append [0]) (mkConst ``Char) ls R,
      mkApp4 (mkConst ``leaf_tail) t ls R refl)
  | .lit (.strVal s), none =>
    let ls := charsE s
    let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``String) (mkApp (mkConst ``String.ofList) ls)
    return (ls, mkApp3 (mkConst ``leaf_end) t ls refl)
  | _, _ =>
    let some (a, b) := appendArgs? t
      | throwError "str_lits: expected a `++` tree of string literals, found{indentExpr t}"
    let (Lb, pb) ← build b tail
    let (La, pa) ← build a (some Lb)
    match tail with
    | some R => return (La, mkAppN (mkConst ``node_tail) #[a, b, La, Lb, R, pa, pb])
    | none => return (La, mkAppN (mkConst ``node_end) #[a, b, La, Lb, pa, pb])

elab "str_lits " c:ident : tactic => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some body := (← getConstInfo n).value?
    | throwError "str_lits: `{n}` has no visible definition"
  let (L, h) ← build body none
  liftMetaTactic1 fun g => do
    let ty ← instantiateMVars (← g.getType)
    let cE := mkConst n
    let abst ← kabstract ty cE
    unless abst.hasLooseBVars do throwError "str_lits: `{n}` does not occur in the goal"
    let motive := Expr.lam `s (mkConst ``String) abst .default
    let g' ← mkFreshExprSyntheticOpaqueMVar (abst.instantiate1 (mkApp (mkConst ``String.ofList) L))
      (← g.getTag)
    g.assign (mkAppN (mkConst ``of_ofList) #[motive, cE, L, h, g'])
    return some g'.mvarId!

end CFSG.KC.StrLits
