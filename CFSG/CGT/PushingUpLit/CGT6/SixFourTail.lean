module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourIdent
public import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def AschbacherSLTail : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G) (R : Subgroup G) [R.Normal], EightCtx Y T R →
      ∀ n : ℕ, 1 ≤ n → IsNaturalSLTwoModule ↥Y n →
        (∀ f : ℕ, ¬ StatedClassicalModel
          (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) StatedLieTag.PSL 2 2 f) →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem aschbacherSixFourCoreSL_of_tail (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hTail : AschbacherSLTail) : AschbacherSixFourCoreSL := by
  intro G _ _ hK hchar Y T hY hYT ⟨n, hn, hnat⟩ R hR hRP hRn hC U₀ hU hU₀T hYU hYs
  have := hRn
  have hctx : EightCtx Y T R := ⟨hchar, hY, hYT, hR, hRP, hRn, hC⟩
  by_cases hf : ∃ f : ℕ, StatedClassicalModel
      (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) StatedLieTag.PSL 2 2 f
  · obtain ⟨f, hf⟩ := hf
    have hnorm : Y.Normal := eight_sl_normal_of_psl2 hctx hn hnat hS h215 hL hf
    exact ⟨Y, le_rfl, hnorm.isSubnormal, hY, Or.inl rfl⟩
  · push Not at hf
    exact hTail G hK hchar Y T R hctx n hn hnat hf U₀ hU hU₀T hYU hYs

theorem aschbacherSixFourCore_of_tail (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hTail : AschbacherSLTail) : AschbacherSixFourCore :=
  aschbacherSixFourCore_of_sl (aschbacherSixFourCoreSL_of_tail hS h215 hL hTail)

end CFSG.CGT.PushingUpLit.CGT6
