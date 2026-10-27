module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def pA : ↥P1408 := ⟨elemA, elemA_mem⟩

@[expose] noncomputable def pZ : ↥P1408 := ⟨elemZ, elemZ_mem⟩

@[expose] noncomputable def pB : ↥P1408 := ⟨elemB, elemB_mem⟩

@[expose] noncomputable def pZ₁ : ↥P1408 := ⟨elemZ₁, elemZ₁_mem⟩

theorem coe_pA : (pA : Equiv.Perm (Fin 1408)) = elemA := rfl
theorem coe_pZ : (pZ : Equiv.Perm (Fin 1408)) = elemZ := rfl
theorem coe_pB : (pB : Equiv.Perm (Fin 1408)) = elemB := rfl
theorem coe_pZ₁ : (pZ₁ : Equiv.Perm (Fin 1408)) = elemZ₁ := rfl

theorem isConj_subtype_iff {M : Type*} [Group M] (P : Subgroup M) {t x : M} (ht : t ∈ P)
    (hx : x ∈ P) : IsConj (⟨t, ht⟩ : ↥P) ⟨x, hx⟩ ↔ x ∈ conjClass P t := by
  rw [isConj_iff, mem_conjClass]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    have := congrArg Subtype.val hc
    simpa using this.symm
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, Subtype.ext (by simp)⟩

theorem isConj_iff_mem_conjClass {M : Type*} [Group M] (P : Subgroup M) (X Y : ↥P) :
    IsConj X Y ↔ (Y : M) ∈ conjClass P (X : M) := isConj_subtype_iff P X.2 Y.2

theorem mem_conjClass_of_conj {M : Type*} [Group M] {P : Subgroup M} {r x y : M} (hy : y ∈ P)
    (h : y⁻¹ * x * y ∈ conjClass P r) : x ∈ conjClass P r := by
  obtain ⟨c, hc, hcr⟩ := mem_conjClass.1 h
  refine mem_conjClass.2 ⟨y * c, P.mul_mem hy hc, ?_⟩
  have : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
  rw [this, hcr]
  group

theorem two_factorization_card_P1408 : (177408000 : ℕ).factorization 2 = 11 := by
  rw [show (177408000 : ℕ) = 2 ^ 11 * 86625 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.EvenSporadicStandard.HNRecog
