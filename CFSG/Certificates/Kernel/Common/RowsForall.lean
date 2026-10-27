module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.HarnessGz
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CFSG.KC.RowsForall

theorem rf_zero {Q : Nat → Prop} (lo : Nat) : ∀ k, lo ≤ k → k < lo → Q k :=
  fun _ h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)

theorem rf_succ {Q : Nat → Prop} {lo m : Nat} (h : ∀ k, lo ≤ k → k < m → Q k) (hm : Q m) :
    ∀ k, lo ≤ k → k < Nat.succ m → Q k := by
  intro k h1 h2
  rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | rfl
  · exact h k h1 h3
  · exact hm

end CFSG.KC.RowsForall

end

open Lean Elab Command Meta

namespace CFSG.KC.RowsForall

meta def rowsOf (b : ByteArray) : Array (Array Nat) :=
  (((String.fromUTF8! b).splitOn "\n").filter (· ≠ "")).toArray.map fun l =>
    ((l.splitOn " ").filter (· ≠ "")).toArray.map String.toNat!

meta partial def exBody (fE k : Expr) (r : Nat) (as : Array Expr) : MetaM Expr := do
  if as.size = r then
    return ← mkEq (mkAppN fE (#[k] ++ as)).headBeta (mkConst ``Bool.true)
  withLocalDeclD ((`a).appendIndexAfter as.size) (mkConst ``Nat) fun a => do
    let body ← exBody fE k r (as.push a)
    mkAppM ``Exists #[← mkLambdaFVars #[a] body]

meta partial def exProof (T : Expr) (as : List Nat) (thm : Expr) : MetaM Expr := do
  match as, T.getAppFnArgs with
  | a :: as, (``Exists, #[α, p]) =>
    let h ← exProof (p.beta #[mkRawNatLit a]).headBeta as thm
    return mkApp4 (mkConst ``Exists.intro [1]) α p (mkRawNatLit a) h
  | [], _ => return thm
  | _, _ => throwError "#kc_rows_forall: unexpected statement {T}"

end CFSG.KC.RowsForall

open CFSG.KC.Gz CFSG.KC.Each CFSG.KC.RowsForall in
elab "#kc_rows_forall " nm:ident f:term:max path:str size:num hash:num lo:num hi:num pre:ident :
    command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let lo := lo.getNat
  let hi := hi.getNat
  let rs := (rowsOf b).filter fun r => lo ≤ r[0]! && r[0]! < hi
  unless rs.map (·[0]!) == (Array.range (hi - lo)).map (lo + ·) do
    throwError "#kc_rows_forall: the rows of {path.getString} in [{lo}, {hi}) are not {lo} … {hi - 1}"
  let r := rs[0]!.size
  unless rs.all (·.size == r) do
    throwError "#kc_rows_forall: the rows of {path.getString} differ in length"
  let fE ← elabCheck f r
  let base := pre.getId
  let env ← getEnv
  liftTermElabM do
    let natT := mkConst ``Nat
    let Q ← withLocalDeclD `k natT fun k => do mkLambdaFVars #[k] (← exBody fE k (r - 1) #[])
    let mut pf := mkApp2 (mkConst ``rf_zero) Q (mkRawNatLit lo)
    for row in rs do
      let i := row[0]!
      let t := base.appendAfter s!"{i}"
      unless env.contains t do throwError "#kc_rows_forall: unknown theorem {t}"
      let h ← exProof (Q.beta #[mkRawNatLit i]).headBeta (row.extract 1 r).toList (mkConst t)
      pf := mkAppN (mkConst ``rf_succ) #[Q, mkRawNatLit lo, mkRawNatLit i, pf, h]
    let leE := mkAppN (mkConst ``LE.le [0]) #[natT, mkConst ``instLENat, mkRawNatLit lo, .bvar 0]
    let ltE := mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, .bvar 1, mkRawNatLit hi]
    let ty := mkForall `k .default natT (mkForall `h₁ .default leE
      (mkForall `h₂ .default ltE (mkApp Q (.bvar 2)).headBeta))
    let name := (← getCurrNamespace) ++ nm.getId
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := pf }
