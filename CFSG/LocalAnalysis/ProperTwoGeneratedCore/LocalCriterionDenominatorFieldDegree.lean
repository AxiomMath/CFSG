module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCommutant

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem rationalCommutant_finrank_dvd [Finite K] [FiniteDimensional K V] [Nontrivial V]
    (T : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Module.finrank K (rationalCommutant T) ∣ Module.finrank K V := by
  let : Field (rationalCommutant T) := (rationalCommutant_isField T hirr).toField
  let : Module (rationalCommutant T) V := (rationalCommutant T).moduleLeft
  let : IsScalarTower K (rationalCommutant T) V := inferInstance
  exact Module.finrank_dvd_finrank_right K (rationalCommutant T) V

theorem rationalCommutant_card_aut [Finite K] [FiniteDimensional K V] [Nontrivial V]
    (T : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Nat.card (rationalCommutant T ≃ₐ[K] rationalCommutant T) =
      Module.finrank K (rationalCommutant T) := by
  classical
  let : Field (rationalCommutant T) := (rationalCommutant_isField T hirr).toField
  let : Finite V := Module.finite_of_finite K
  let : Finite (Module.End K V) := Finite.of_injective
    (fun S : Module.End K V => (S : V → V)) DFunLike.coe_injective
  let : Finite (rationalCommutant T) := inferInstance
  exact IsGalois.card_aut_eq_finrank K (rationalCommutant T)

theorem rationalCommutant_card_aut_dvd_four [Finite K] [FiniteDimensional K V]
    [Nontrivial V] (T : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdim : Module.finrank K V = 4) :
    Nat.card (rationalCommutant T ≃ₐ[K] rationalCommutant T) ∣ 4 := by
  rw [rationalCommutant_card_aut T hirr, ← hdim]
  exact rationalCommutant_finrank_dvd T hirr

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
