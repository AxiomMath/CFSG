module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {P : Type*} [Group P] {W : Subgroup P} [W.Normal]

theorem sq_mem_of_quotient (hU : ∀ u : P ⧸ W, u ^ 2 = 1) (x : P) : x ^ 2 ∈ W := by
  have h := hU (x : P ⧸ W)
  rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h

@[expose] noncomputable def squareMap (hWc : W ≤ center P) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hU : ∀ u : P ⧸ W, u ^ 2 = 1) : P ⧸ W → W :=
  Quotient.lift (fun x : P => (⟨x ^ 2, sq_mem_of_quotient hU x⟩ : W)) (by
    intro x y hxy
    have hw : x⁻¹ * y ∈ W := QuotientGroup.leftRel_apply.1 hxy
    apply Subtype.ext
    change x ^ 2 = y ^ 2
    have hc : ∀ g : P, g * (x⁻¹ * y) = (x⁻¹ * y) * g := fun g => mem_center_iff.1 (hWc hw) g
    have hy : y = x * (x⁻¹ * y) := by group
    rw [hy, sq, sq, mul_assoc, ← mul_assoc (x⁻¹ * y), ← hc x, mul_assoc, ← mul_assoc x,
      ← sq (x⁻¹ * y), hW2 _ hw, mul_one, ← sq])

end CFSG.LocalAnalysis.ComponentInitial
