module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightAlt

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement Pointwise

@[expose] def AschbacherSixFourCoreSL : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G), InClassX ↥Y → Y = ⁅jIn (T : Subgroup G), Y⁆ →
      (∃ n : ℕ, 1 ≤ n ∧ IsNaturalSLTwoModule ↥Y n) →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) →
        oTwoIn (Subgroup.normalizer (R : Set G)) = R → R.Normal →
        Subgroup.centralizer (omegaOneCenterIn R : Set G) = R →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem aschbacherSixFourCore_of_sl (h : AschbacherSixFourCoreSL) : AschbacherSixFourCore := by
  intro G _ _ hK hchar Y T hY hYT R hR hRP hRn hC U₀ hU hU₀T hYU hYs
  rcases hY.2 with ⟨a, ha, hnat⟩ | ⟨n, hn, hnat⟩
  · obtain ⟨φ, hφ⟩ := isNaturalAltModule_iff.mp hnat
    have hctx : EightCtx Y T R := ⟨hchar, hY, hYT, hR, hRP, hRn, hC⟩
    have hnorm : Y.Normal := eight_alt_normal hctx ha hφ
    exact ⟨Y, le_rfl, hnorm.isSubnormal, hY, Or.inl rfl⟩
  · exact h G hK hchar Y T hY hYT ⟨n, hn, hnat⟩ R hR hRP hRn hC U₀ hU hU₀T hYU hYs

end CFSG.CGT.PushingUpLit.CGT6
