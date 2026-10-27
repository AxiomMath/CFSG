module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ClassicalLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3D4Main
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley Matrix


theorem D4.BZ_sq : D4.BZ * D4.BZ = 1 := by decide +kernel

theorem D4.castM_BZ_isUnit_det (K : Type) [Field K] : IsUnit (D4.castM K D4.BZ).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := D4.castM K D4.BZ)
  rw [← map_mul, D4.BZ_sq, map_one]

theorem no_hsType_chevalley_D4 {S : Type} [Group S] [Finite S] {p f : ℕ} (hp3 : p ≠ 3)
    (hM : ChevalleyExceptionalModel S .trialityD4 p f) (K : Subgroup S) (hK : HSType ↥K) :
    False := by
  obtain ⟨⟨hp, hf, _⟩, hM2⟩ := hM
  obtain ⟨K', _, _, hcard, σ, hσ, ⟨e⟩⟩ := hM2
  set H := twistedFixedGroup .D4 K' σ with hH
  obtain ⟨Yh, hYh⟩ := exists_hsType_of_quotient (center ↥⁅H, H⁆) le_rfl e K hK
  have hY := hsType_map_of_injective (⁅H, H⁆.subtype) ⁅H, H⁆.subtype_injective Yh hYh
  have hHle : H ≤ adjointGroup Tag.D4 K' := inf_le_left
  have hcomm : ⁅H, H⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)
  have hle : Yh.map ⁅H, H⁆.subtype ≤ adjointGroup Tag.D4 K' := by
    rintro _ ⟨y, _, rfl⟩
    exact hHle (hcomm y.2)
  obtain ⟨Y₂, horth, hq, ⟨e₂⟩⟩ := D4.exists_transfer_D4 K' (Yh.map ⁅H, H⁆.subtype) hle hY.1
  have hY₂ : HSType ↥Y₂ := HSType.of_equiv e₂ hq hY
  have hchar : ringChar K' = p := by
    refine CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq (f := f * 3) hp (by omega) ?_
    rw [hcard]
    show (p ^ f) ^ 3 = p ^ (f * 3)
    rw [pow_mul]
  haveI : Finite K' := inferInstance
  exact no_hsType_card_eq_eight (F := K') (ι := Fin 8) (by rw [hchar]; exact hp3)
    (by simp) (D4.castM K' D4.BZ) (D4.castM_BZ_isUnit_det K') Y₂ hY₂ horth

end CFSG.ComponentClassification.CatFC.KGHS3
