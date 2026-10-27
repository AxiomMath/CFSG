module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

abbrev PW : Type := List (Bool × ℕ)

@[expose] def evalPW {G : Type*} [Group G] (a b : G) : PW → G
  | [] => 1
  | (c, e) :: w => (if c then b else a) ^ e * evalPW a b w

@[expose] def evalIdx {G : Type*} [Group G] (xs : List G) : List (ℕ × ℕ) → G
  | [] => 1
  | (i, e) :: w => xs.getD i 1 ^ e * evalIdx xs w

structure PGen where
  p : ℕ
  z : PW
  ts : List PW
  ns : List (PW × ℕ × ℕ)
  ms : List (PW × ℕ)
  wa : List (ℕ × ℕ)
  wb : List (ℕ × ℕ)

@[expose] def PGen.regs {G : Type*} [Group G] (a b : G) (c : PGen) : List G :=
  c.ns.map (fun n => evalPW a b n.1) ++ c.ms.map (fun m => evalPW a b m.1)

@[expose] def PGen.holds {G : Type*} [Group G] (a b : G) (c : PGen) : Prop :=
  evalPW a b c.z ^ c.p = 1 ∧ evalPW a b c.z ≠ 1 ∧
  (∀ w ∈ c.ts, evalPW a b w * evalPW a b w = 1 ∧ evalPW a b w ≠ 1 ∧
      evalPW a b c.z * evalPW a b w = evalPW a b w * evalPW a b c.z) ∧
  (∀ n ∈ c.ns, evalPW a b n.1 * evalPW a b c.z * (evalPW a b n.1)⁻¹ = evalPW a b c.z ^ n.2.1 ∧
      evalPW a b n.1 * evalPW a b c.z ^ n.2.2 * (evalPW a b n.1)⁻¹ = evalPW a b c.z) ∧
  (∀ m ∈ c.ms, ∃ w ∈ c.ts, evalPW a b m.1 * evalPW a b w = evalPW a b w * evalPW a b m.1) ∧
  a = evalIdx (c.regs a b) c.wa ∧ b = evalIdx (c.regs a b) c.wb

@[expose] def PGen.check {G : Type*} [Group G] [DecidableEq G] (a b : G) (c : PGen) : Bool :=
  let z := evalPW a b c.z
  decide (z ^ c.p = 1) && decide (z ≠ 1) &&
  c.ts.all (fun w =>
    let t := evalPW a b w
    decide (t * t = 1) && decide (t ≠ 1) && decide (z * t = t * z)) &&
  c.ns.all (fun n =>
    let x := evalPW a b n.1
    decide (x * z * x⁻¹ = z ^ n.2.1) && decide (x * z ^ n.2.2 * x⁻¹ = z)) &&
  c.ms.all (fun m =>
    let x := evalPW a b m.1
    c.ts.any (fun w => let t := evalPW a b w; decide (x * t = t * x))) &&
  decide (a = evalIdx (c.regs a b) c.wa) && decide (b = evalIdx (c.regs a b) c.wb)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
