module

public import CFSG.ClassicalInvolution.Q3.Q3T8AF05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] [Finite G]


theorem exists_conj_lift_involutions {X Λ : Subgroup G}
    (hΛ : Λ ≤ Subgroup.normalizer (X : Set G)) {z t t' : G} (hzΛ : z ∈ Λ) (hz2 : z * z = 1)
    (hzX : ∀ x ∈ X, ⁅x, z⁆ ∈ oddCoreOf X) (htX : t ∈ X) (ht'X : t' ∈ X) (ht2 : t * t = 1)
    (ht'2 : t' * t' = 1) (ht1 : t ≠ 1) (ht'1 : t' ≠ 1) (hzt : z * t = t * z)
    (hzt' : z * t' = t' * z)
    (hconj : CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.InvolutionsConj
      (↥X ⧸ classicalInvolutionOddCore ↥X)) :
    ∃ y ∈ X, y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t' := by
  classical
  set O : Subgroup G := oddCoreOf X with hOdef
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard X
  have hOX : O ≤ X := oddCoreOf_le_self X
  have hconjO : ∀ g ∈ Λ, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer (hΛ hg)) o).mp ho
  have hCz : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * z * g⁻¹ = z := fun g hg => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  set M : Subgroup ↥X := classicalInvolutionOddCore ↥X with hM
  set π : ↥X →* (↥X ⧸ M) := QuotientGroup.mk' M with hπ
  have hker : ∀ a : ↥X, π a = 1 → (a : G) ∈ O := fun a h =>
    mem_oddCoreOf_iff.mpr ⟨a.2, (QuotientGroup.eq_one_iff _).mp h⟩
  have hker' : ∀ a : ↥X, (a : G) ∈ O → π a = 1 := fun a h =>
    (QuotientGroup.eq_one_iff _).mpr (mem_oddCoreOf_iff.mp h).2
  have hnot : ∀ c : G, c ∈ X → c * c = 1 → c ≠ 1 → ∀ hcX : c ∈ X, π ⟨c, hcX⟩ ≠ 1 := by
    intro c _ hc2 hc1 hcX h
    exact hc1 (eq_one_of_isPGroup_of_mem_odd hOodd (hker _ h)
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2))
  set X₁ : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G) with hX₁
  have hlift : ∀ q : ↥X ⧸ M, ∃ x : G, ∃ hx : x ∈ X₁, π ⟨x, hx.1⟩ = q := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨o, ho, hoz⟩ := exists_mul_mem_centralizer hOodd hconjO hzΛ hz2 (hzX a a.2)
    have hoX : o⁻¹ ∈ X := X.inv_mem (hOX ho)
    refine ⟨o⁻¹ * a, ⟨X.mul_mem hoX a.2, hoz⟩, ?_⟩
    have e : (⟨o⁻¹ * a, X.mul_mem hoX a.2⟩ : ↥X) = ⟨o⁻¹, hoX⟩ * a := rfl
    rw [e, map_mul, hker' ⟨o⁻¹, hoX⟩ (O.inv_mem ho), one_mul]
    rfl
  have hOodd₁ : Odd (Nat.card (O ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)) :=
    hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hu2 : π ⟨t, htX⟩ * π ⟨t, htX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htX⟩ * ⟨t, htX⟩ : ↥X) = 1 := Subtype.ext ht2
    rw [this, map_one]
  obtain ⟨gq, hgq⟩ := hconj _ _ hu2
    (show π ⟨t', ht'X⟩ * π ⟨t', ht'X⟩ = 1 by
      rw [← map_mul]
      have : (⟨t', ht'X⟩ * ⟨t', ht'X⟩ : ↥X) = 1 := Subtype.ext ht'2
      rw [this, map_one]) (hnot t htX ht2 ht1 htX) (hnot t' ht'X ht'2 ht'1 ht'X)
  obtain ⟨x₁, hx₁, hπx₁⟩ := hlift gq
  have htX₁ : t ∈ X₁ := ⟨htX, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hux : x₁ * t * x₁⁻¹ ∈ X₁ := X₁.mul_mem (X₁.mul_mem hx₁ htX₁) (X₁.inv_mem hx₁)
  have hπu : π ⟨x₁ * t * x₁⁻¹, hux.1⟩ = π ⟨t', ht'X⟩ := by
    have e : (⟨x₁ * t * x₁⁻¹, hux.1⟩ : ↥X) = ⟨x₁, hx₁.1⟩ * ⟨t, htX⟩ * ⟨x₁, hx₁.1⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hπx₁, ← hgq]
  have ht'X₁ : t' ∈ X₁ := ⟨ht'X, Subgroup.mem_centralizer_singleton_iff.mpr hzt'.symm⟩
  have hinv : (x₁ * t * x₁⁻¹)⁻¹ * t' ∈ O ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine ⟨?_, (X₁.mul_mem (X₁.inv_mem hux) ht'X₁).2⟩
    have h1 : π ((⟨x₁ * t * x₁⁻¹, hux.1⟩ : ↥X)⁻¹ * ⟨t', ht'X⟩) = 1 := by
      rw [map_mul, map_inv, hπu, inv_mul_cancel]
    exact hker _ h1
  have hu2' : (x₁ * t * x₁⁻¹) * (x₁ * t * x₁⁻¹) = 1 := by
    calc x₁ * t * x₁⁻¹ * (x₁ * t * x₁⁻¹) = x₁ * (t * t) * x₁⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨ν, hν, hνe⟩ := CFSG.ClassicalInvolution.Q3.Q3T8.AF.exists_conj_of_inv_mul_mem hu2' ht'2
    hOodd₁ hinv
  refine ⟨ν * x₁, X.mul_mem (hOX hν.1) hx₁.1, ?_, ?_⟩
  · calc ν * x₁ * z * (ν * x₁)⁻¹ = ν * (x₁ * z * x₁⁻¹) * ν⁻¹ := by group
      _ = ν * z * ν⁻¹ := by rw [hCz x₁ hx₁.2]
      _ = z := hCz ν hν.2
  · calc ν * x₁ * t * (ν * x₁)⁻¹ = ν * (x₁ * t * x₁⁻¹) * ν⁻¹ := by group
      _ = t' := hνe.symm

end Glue

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
