module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.Wreathed.ReducedCentralizerSylow

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem mem_coordinateU_of_forall_commute {K : Type*} [Field K] {σ : Equiv.Perm (Omega K)}
    (hσ : ∀ b : K, σ * translation K b = translation K b * σ) : σ ∈ coordinateU K := by
  have hcomm : ∀ (b : K) (ω : Omega K), σ (translation K b ω) = translation K b (σ ω) :=
    fun b ω => congrArg (fun π : Equiv.Perm (Omega K) => π ω) (hσ b)
  have hnone : σ none = none := by
    cases h : σ none with
    | none => rfl
    | some y =>
      exfalso
      have h1 := hcomm 1 none
      rw [translation_none, h, translation_some] at h1
      have h2 : y = y + 1 := Option.some_injective _ h1
      exact one_ne_zero (by linear_combination -h2 : (1 : K) = 0)
  obtain ⟨b, hb⟩ : ∃ b : K, σ (some 0) = some b := by
    cases h : σ (some 0) with
    | none => exact absurd (σ.injective (h.trans hnone.symm)) (Option.some_ne_none 0)
    | some b => exact ⟨b, rfl⟩
  have hσeq : σ = translation K b := by
    ext ω
    cases ω with
    | none => rw [hnone, translation_none]
    | some a =>
      have h1 := hcomm a (some 0)
      rw [translation_some, zero_add, hb, translation_some] at h1
      rw [h1, translation_some, add_comm]
  rw [hσeq]
  exact Subgroup.subset_closure ⟨b, rfl⟩

theorem isElementaryAbelian_multiplicative (p : ℕ) (K : Type*) [Field K] [CharP K p] :
    IsElementaryAbelian p (Multiplicative K) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    [IsElementaryAbelian p A] (e : A ≃* B) : IsElementaryAbelian p B :=
  CFSG.IsElementaryAbelian.of_mulEquiv e inferInstance

end CFSG.Wreathed.ReducedCentralizerSylow
