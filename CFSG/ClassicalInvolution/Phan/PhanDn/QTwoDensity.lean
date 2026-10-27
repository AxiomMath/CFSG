module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoDensityCheck
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoGammaThree

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem exists_flipflopPt_orth_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (f : Fin 3 ⊕ Fin 3 → K) :
    ∃ p, IsFlipflopPt σ p ∧ ∀ v ∈ p, polar (quadPlus 3 K) v f = 0 ∧ flipHerm σ v f = 0 := by
  obtain ⟨w, hσw, hw⟩ := QTwoGammaThree.exists_sigma_eq_add_one hσ hK
  obtain ⟨F, rfl⟩ := QTwoGammaThree.exists_lift hK hw f
  obtain ⟨u, hq, hn, hp, hh⟩ := QTwoGammaThree.density_spec F
  have hq' : quadPlus 3 K (QTwoGammaThree.lift w u) = 0 := by
    rw [QTwoGammaThree.quadPlus_lift hw, hq]
    rfl
  have hn' : flipHerm σ (QTwoGammaThree.lift w u) (QTwoGammaThree.lift w u) = 1 := by
    rw [QTwoGammaThree.flipHerm_lift hw hσw, hn]
    rfl
  have hne : QTwoGammaThree.lift w u ≠ 0 := by
    intro h
    rw [h, flipHerm_zero_left] at hn'
    exact zero_ne_one hn'
  refine ⟨K ∙ QTwoGammaThree.lift w u,
    (isFlipflopPt_span_singleton_iff hne).mpr ⟨hq', by rw [hn']; exact one_ne_zero⟩, ?_⟩
  intro v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [polar_smul_left, flipHerm_smul_left, QTwoGammaThree.polar_lift hw,
    QTwoGammaThree.flipHerm_lift hw hσw, hp, hh]
  exact ⟨by simp [QTwoGammaThree.ι], by simp [QTwoGammaThree.ι]⟩

end CFSG.ClassicalInvolution.PhanDn
