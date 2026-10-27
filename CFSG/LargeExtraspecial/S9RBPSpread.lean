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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.S9.RB

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem map_mkQ_inf_of_le {V A B : Submodule (ZMod 2) M} (hVA : V ≤ A) :
    A.map V.mkQ ⊓ B.map V.mkQ = (A ⊓ B).map V.mkQ := by
  refine le_antisymm ?_ (Submodule.map_inf_le _)
  rintro z ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
  have hab : b - a ∈ V := (Submodule.Quotient.eq V).mp hba
  have hbA : b ∈ A := by
    have := A.add_mem ha (hVA hab)
    rwa [add_sub_cancel] at this
  exact ⟨b, ⟨hbA, hb⟩, hba⟩

theorem card_le_five_of_pairwise_inf_eq_bot [Finite M] {Z : Submodule (ZMod 2) M}
    (hZ : Nat.card Z ≤ 16) {ι : Type*} [Finite ι] (ℓ : ι → Submodule (ZMod 2) M)
    (hle : ∀ i, ℓ i ≤ Z) (h4 : ∀ i, 4 ≤ Nat.card (ℓ i))
    (hdisj : ∀ i j, i ≠ j → ℓ i ⊓ ℓ j = ⊥) : Nat.card ι ≤ 5 := by
  classical
  have := Fintype.ofFinite M
  have := Fintype.ofFinite ι
  let A : ι → Finset M := fun i => (Finset.univ.filter fun x => x ∈ ℓ i) \ {0}
  have hA : ∀ i, 3 ≤ (A i).card := by
    intro i
    have hc : (Finset.univ.filter fun x => x ∈ ℓ i).card = Nat.card (ℓ i) := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp)
    have h0 : ({0} : Finset M) ⊆ Finset.univ.filter fun x => x ∈ ℓ i := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      simp [hx, zero_mem]
    have := Finset.card_sdiff_of_subset h0
    simp only [A]
    rw [this, hc, Finset.card_singleton]
    have := h4 i
    omega
  have hpd : (Set.univ : Set ι).PairwiseDisjoint A := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun x hxi hxj => ?_
    simp only [A, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hxi hxj
    have : x ∈ ℓ i ⊓ ℓ j := ⟨hxi.1, hxj.1⟩
    rw [hdisj i j hij, Submodule.mem_bot] at this
    exact hxi.2 this
  have hsub : Finset.univ.biUnion A ⊆ (Finset.univ.filter fun x => x ∈ Z) \ {0} := by
    intro x hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    simp only [A, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hxi ⊢
    exact ⟨hle i hxi.1, hxi.2⟩
  have hcardZ : ((Finset.univ.filter fun x => x ∈ Z) \ {0}).card ≤ 15 := by
    have hc : (Finset.univ.filter fun x => x ∈ Z).card = Nat.card Z := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by simp)
    have h0 : ({0} : Finset M) ⊆ Finset.univ.filter fun x => x ∈ Z := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      simp [hx, zero_mem]
    rw [Finset.card_sdiff_of_subset h0, hc, Finset.card_singleton]
    omega
  have hU := Finset.card_biUnion (s := Finset.univ) (t := A) (fun i _ j _ hij => hpd
    (Set.mem_univ i) (Set.mem_univ j) hij)
  have hsum : 3 * Fintype.card ι ≤ ∑ i, (A i).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => hA i
  have := Finset.card_le_card hsub
  rw [Nat.card_eq_fintype_card]
  omega

end CFSG.LargeExtraspecial.S9.RB
