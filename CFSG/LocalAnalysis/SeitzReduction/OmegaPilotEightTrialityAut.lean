module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialityModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryAut)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

variable (F) in
@[expose] noncomputable def plusFourGraphAut :
    d4DiagramGroup →* MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) :=
  (MulAut.congr (spin8Equiv F)).toMonoidHom.comp spinGraphAut

theorem plusFourGraphAut_apply (π : d4DiagramGroup)
    (y : matrixProjectiveDerived (coordinateQuadPlus 4 F)) :
    plusFourGraphAut F π y = spin8Equiv F (spinGraphAut π ((spin8Equiv F).symm y)) := rfl

theorem plusFourGraphAut_x (π : d4DiagramGroup) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) (c : F) :
    plusFourGraphAut F π (spin8Equiv F (SpinPlus.x 4 F d4_three_le γ c)) =
      spin8Equiv F (SpinPlus.x 4 F d4_three_le (fundPerm (π : Equiv.Perm (Fin 4)) γ) c) := by
  rw [plusFourGraphAut_apply, MulEquiv.symm_apply_apply, spinGraphAut_x π hγ]

theorem plusFour_mulAut_ext {α β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F))}
    (h : ∀ γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots, ∀ c : F,
      α (spin8Equiv F (SpinPlus.x 4 F d4_three_le γ c)) =
        β (spin8Equiv F (SpinPlus.x 4 F d4_three_le γ c))) : α = β := by
  have h' : (MulAut.congr (spin8Equiv F)).symm α = (MulAut.congr (spin8Equiv F)).symm β := by
    refine spin8_mulAut_ext fun γ hγ c => ?_
    change (spin8Equiv F).symm (α (spin8Equiv F _)) = (spin8Equiv F).symm (β (spin8Equiv F _))
    rw [h γ hγ c]
  exact (MulAut.congr (spin8Equiv F)).symm.injective h'

theorem symmetryAut_eq_plusFourGraphAut_d4ForkSym :
    symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) = plusFourGraphAut F d4ForkSym :=
  plusFour_mulAut_ext fun γ hγ c => by
    rw [symmetryAut_spin8Equiv_x hγ, plusFourGraphAut_x d4ForkSym hγ]
    rfl

variable (F) in
@[expose] noncomputable def plusFourTriality :
    MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) :=
  plusFourGraphAut F d4TrialitySym

theorem plusFourTriality_x {γ : Fin 4 → ℤ} (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots)
    (c : F) :
    plusFourTriality F (spin8Equiv F (SpinPlus.x 4 F d4_three_le γ c)) =
      spin8Equiv F (SpinPlus.x 4 F d4_three_le (fundPerm d4TrialityPerm γ) c) :=
  plusFourGraphAut_x d4TrialitySym hγ c

theorem plusFourTriality_pow_three : plusFourTriality F ^ 3 = 1 := by
  rw [plusFourTriality, ← map_pow, d4TrialitySym_pow_three, map_one]

theorem symmetryAut_conj_plusFourTriality :
    symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3) * plusFourTriality F *
        (symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3))⁻¹ =
      (plusFourTriality F)⁻¹ := by
  have hinv : d4ForkSym⁻¹ = d4ForkSym := inv_eq_of_mul_eq_one_right d4ForkSym_mul_self
  rw [symmetryAut_eq_plusFourGraphAut_d4ForkSym, plusFourTriality, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv, hinv, d4ForkSym_conj_d4TrialitySym]

theorem plusFourTriality_mul_fieldAutHom (σ : F ≃+* F) :
    plusFourTriality F * fieldAutHom F 4 σ = fieldAutHom F 4 σ * plusFourTriality F :=
  plusFour_mulAut_ext fun γ hγ c => by
    have h' : fundPerm d4TrialityPerm γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots :=
      fundPerm_mem_spinRoots d4TrialitySym hγ
    rw [MulAut.mul_apply, MulAut.mul_apply, fieldAutHom_spin8Equiv_x σ hγ, plusFourTriality_x hγ,
      plusFourTriality_x hγ, fieldAutHom_spin8Equiv_x σ h']

end CFSG.SeitzReduction.OmegaPilot
