module

public import CFSG.LieType.SeitzGeneration.QuasiHigh2Linear
import CFSG.HardMathSupport.Solomon.Coordinator.L3AField

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.LieType.Chevalley

open CFSG.HardMathSupport.Solomon.LocalBalance (IsFieldAutThree)
open CFSG.RankThree.PartTwo.KFacts (centerDescend psuField psuPrimeFormEquiv congr_psuField)
open CFSG.LocalAnalysis.GLTheoremB (quotientCenterAut')

theorem isFieldAutThree_pow_of_not_mem_primeFormD {K : Type} [Group K] {ℓ f : ℕ}
    {Kf : Type} [Field Kf] (h : UnitaryFieldData ℓ f Kf) (hne : ¬(3 = 3 ∧ ℓ ^ f = 2))
    (hℓ : 3 ≠ ℓ) (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf 3))
    {α : MulAut K} (hα3 : α ^ 3 = 1)
    (hα : QuasiHigh2.modelAut θ α ∉ primeFormD h (idGram Kf 3)) (k : ℕ) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsFieldAutThree (α ^ k) := by
  classical
  set β : MulAut (primeFormP h (idGram Kf 3)) := QuasiHigh2.modelAut θ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβ1 : β ≠ 1 := fun h1 => hα (by rw [h1]; exact one_mem _)
  set Θ := primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hne with hΘ
  have hkerΘ := ker_primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hne
  have hσ1 : Θ β ≠ 1 := fun h1 => hα (by rw [← hkerΘ]; exact h1)
  have hσ3 : Θ β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hσord : orderOf (Θ β) = 3 := orderOf_eq_prime hσ3 hσ1
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h (le_refl 3) hne
      Nat.prime_three (by norm_num) hℓ β hβord (Θ β) rfl hσord
  set σ := Θ β with hσdef
  set pPE := psuPrimeFormEquiv h with hpPE
  set cM := primeFormConjHom h (idGram Kf 3) M with hcM
  set eU : K ⧸ Subgroup.center K ≃* unitaryPSU h 3 := θ.trans pPE.symm with heU
  set γ : MulAut (unitaryPSU h 3) := MulAut.congr pPE.symm cM with hγ
  have hβeq : β = cM * primeFormFieldHom h isPrimeFormGram_one σ * cM⁻¹ := by
    rw [← hM]
    group
  have hcongr_trans : ∀ x : MulAut (K ⧸ Subgroup.center K),
      MulAut.congr pPE (MulAut.congr eU x) = MulAut.congr θ x := fun x => by
    ext y
    simp [heU, hpPE, MulAut.congr_apply]
  have hcongr_γ : MulAut.congr pPE γ = cM := by
    ext y
    simp [hγ, MulAut.congr_apply]
  have hconj : ∀ k : ℕ, MulAut.congr eU (centerDescend K (α ^ k)) =
      γ * psuField h (σ ^ k) * γ⁻¹ := by
    intro k
    apply (MulAut.congr pPE).injective
    have e1 : MulAut.congr pPE (MulAut.congr eU (centerDescend K (α ^ k))) = β ^ k := by
      have hcd : centerDescend K (α ^ k) = quotientCenterAut' K (α ^ k) := rfl
      rw [hcd, hcongr_trans, map_pow (quotientCenterAut' K), map_pow (MulAut.congr θ)]
      rfl
    have e2 : MulAut.congr pPE (γ * psuField h (σ ^ k) * γ⁻¹) =
        cM * primeFormFieldHom h isPrimeFormGram_one σ ^ k * cM⁻¹ := by
      rw [map_mul, map_mul, map_inv, hcongr_γ, congr_psuField, map_pow]
    rw [e1, e2, hβeq, conj_pow]
  refine Or.inr (Or.inr ?_)
  refine CFSG.HardMathSupport.Solomon.Coordinator.isFieldAutPSU3_of_data h eU (σ ^ k) ?_ γ
    (hconj k)
  have : (σ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one this)

end CFSG.LieType.SeitzGeneration.QuasiHigh5