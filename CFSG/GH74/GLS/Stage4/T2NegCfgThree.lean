module

public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeSkel
public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeMat
public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeEx

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem ch6T2NegCfgMod_three : Ch6T2NegCfgMod 3 := by
  intro G _ _ Gs _ q z K₁ K₂ F₁ F₂ _ _ t hSet hRem hq4
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨T₁, T₂, x₁, x₂, w₁, w₂, s, sk⟩ := negSkel_exists hSet hRem
    (fun g hg2 => negFactor_exists hSet.card₁ hq4 g hg2)
    (fun g hg2 => negFactor_exists hSet.card₂ hq4 g hg2)
  exact ⟨x₁ * x₂, T₁ ⊔ T₂ ⊔ Subgroup.zpowers s, w₁, w₂, ch6NegCfg_of_skel hSet hRem sk⟩

end CFSG.GH74.GLS.Stage4.Rest
