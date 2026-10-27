module

public import CFSG.CGT.PushingUpLit.CGT6.SixFiveHolds
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

@[expose] def AschbacherSixFourNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G), InClassX ↥Y → Y = ⁅jIn (T : Subgroup G), Y⁆ →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) →
        oTwoIn (Subgroup.normalizer (R : Set G)) = R → R.Normal →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem aschbacherSixFourNormal_iff : AschbacherSixFourNormal ↔
    ∀ (G : Type) [Group G] [Finite G], SixFourNormalFor G := by
  constructor
  · intro h G _ _ hK hchar Y T R U₀ ⟨hY, hYT, hR, hRP, hU, hU₀T, hYU, hYs⟩ hRn
    exact h G hK hchar Y T hY hYT R hR hRP hRn U₀ hU hU₀T hYU hYs
  · intro h G _ _ hK hchar Y T hY hYT R hR hRP hRn U₀ hU hU₀T hYU hYs
    exact h G hK hchar Y T R U₀ ⟨hY, hYT, hR, hRP, hU, hU₀T, hYU, hYs⟩ hRn

end CFSG.CGT.PushingUpLit.CGT6
