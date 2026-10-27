module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G]

def mulOfCommute (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ↥A × ↥B →* G :=
  MonoidHom.mk' (fun p => (p.1 : G) * (p.2 : G)) (fun p q => by
    have h : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) := hc q.1 q.1.2 p.2 p.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_assoc]
    congr 1
    rw [← mul_assoc, h, mul_assoc])

theorem mulOfCommute_apply (A B : Subgroup G) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (p : ↥A × ↥B) : mulOfCommute A B hc p = (p.1 : G) * (p.2 : G) := by
  unfold mulOfCommute
  rw [MonoidHom.mk'_apply]

theorem card_sup_mul_card_inf [Finite G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hrange : (mulOfCommute A B hc).range = A ⊔ B := by
    apply le_antisymm
    · intro y hy
      obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [mulOfCommute_apply]
      exact mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · apply sup_le
      · intro a ha
        exact MonoidHom.mem_range.mpr ⟨(⟨a, ha⟩, 1), by simp [mulOfCommute_apply]⟩
      · intro b hb
        exact MonoidHom.mem_range.mpr ⟨(1, ⟨b, hb⟩), by simp [mulOfCommute_apply]⟩
  have hker : Nat.card (mulOfCommute A B hc).ker = Nat.card ↥(A ⊓ B) := by
    have hmem : ∀ p : (mulOfCommute A B hc).ker,
        (p.1.1 : G) * (p.1.2 : G) = 1 := fun p => by
      have h := MonoidHom.mem_ker.mp p.2
      rwa [mulOfCommute_apply] at h
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1.1 : G), Subgroup.mem_inf.mpr ⟨p.1.1.2, by
          have h : (p.1.1 : G) = (p.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left (hmem p)
          rw [h]
          exact B.inv_mem p.1.2.2⟩⟩
        invFun := fun g => ⟨(⟨(g : G), (Subgroup.mem_inf.mp g.2).1⟩,
          ⟨(g : G)⁻¹, B.inv_mem (Subgroup.mem_inf.mp g.2).2⟩), by
            rw [MonoidHom.mem_ker, mulOfCommute_apply]
            simp⟩
        left_inv := fun p => Subtype.ext (Prod.ext (Subtype.ext rfl)
          (Subtype.ext (inv_eq_of_mul_eq_one_right (hmem p))))
        right_inv := fun g => Subtype.ext rfl }
  have h1 := Subgroup.card_ker_mul_card_range (mulOfCommute A B hc)
  rw [hker, hrange, Nat.card_prod] at h1
  rw [mul_comm]
  exact h1

theorem card_mul_le_card_sup_mul_of_inf_le [Finite G] (A B W : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) [Finite W] (hW : A ⊓ B ≤ W) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥(A ⊔ B) * Nat.card ↥W := by
  rw [← card_sup_mul_card_inf A B hc]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hW)

end CFSG.HardMathSupport.Timmesfeld.Proving

end
