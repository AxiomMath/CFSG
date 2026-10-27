module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSocle
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddAssembly
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenAssembly

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup

variable {Y : Type} [Group Y] [Finite Y] {p m : ℕ}

theorem false_of_noSmallComponent (hW : ExcSelector.NoSmallComponent Y) (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (h16 : 16 ∣ p ^ (2 * m) - 1) {τ : MulAut Y}
    (hτ : orderOf τ = 2)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) : False := by
  have hτ2 : τ ^ 2 = 1 := by
    rw [← hτ]
    exact pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    norm_num at hτ
  exact hW τ hτ2 hτ1 (GSThmB.layerIn (fixedPoints τ)) (isComponentOf_layerIn hL)
    (layerIn_subgroupOf_normal _) (smallSource_layerIn hp hp2 hm h16 hL)

theorem hinFor_chevalleyExceptional :
    HinFor fun Y _ => ∃ (t : Assembly.LowTwoRank.StatedLieTag) (ℓ f : ℕ),
      t ∈ Blueprint.chevalleyExceptionalTags ∧ Blueprint.ChevalleyExceptionalModel Y t ℓ f := by
  intro Y _ _ _ ⟨t, ℓ, f, _, hY⟩ _ p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  have hW : ExcSelector.NoSmallComponent Y := by
    by_cases hℓ : ℓ = 2
    · subst hℓ
      exact ExcSelector.noSmallComponent_of_model_even hY
    · exact ExcSelector.noSmallComponent_of_model_odd hℓ hY
  exact false_of_noSmallComponent hW hp hp2 hm h16 hτ hL

end CFSG.ComponentClassification.HarrisLit.Hin
