module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourTail
public import CFSG.CGT.PushingUpLit.CGT6.SixFourOrders

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open scoped commutatorElement Pointwise

abbrev SLLam {G : Type} [Group G] (R : Subgroup G) [R.Normal] (T : Sylow 2 G) : Type :=
  ↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)

@[expose] def AschbacherSLTail' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G) (R : Subgroup G) [R.Normal], EightCtx Y T R →
      ∀ n : ℕ, 1 ≤ n → IsNaturalSLTwoModule ↥Y n →
        (∀ f : ℕ, ¬ StatedClassicalModel (SLLam R T) StatedLieTag.PSL 2 2 f) →
        (∀ a : ℕ, ¬ CFSG.Blueprint.LieModel (SLLam R T) .twistedB2 0 2 (2 * a + 1)) →
        ¬ CFSG.Blueprint.NativeSporadic.IsSporadic (SLLam R T) .M22 →
        ¬ CFSG.Blueprint.NativeSporadic.IsSporadic (SLLam R T) .M23 →
        ¬ CFSG.Blueprint.NativeSporadic.IsSporadic (SLLam R T) .M24 →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

section Certified


theorem aschbacherSLTail_of_tail' (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hT : AschbacherSLTail') : AschbacherSLTail := by
  intro G _ _ hK hchar Y T R _ hctx n hn hnat hf U₀ hU hU₀T hYU hYs
  refine hT G hK hchar Y T R hctx n hn hnat hf (fun a hsz => ?_) (fun hM => ?_) (fun hM => ?_)
    (fun hM => ?_) U₀ hU hU₀T hYU hYs
  · exact eight_sl_not_sz hctx hn hnat hS h215 hL hsz
  · exact eight_sl_not_m2j hctx hn hnat hS h215 hL (Or.inl hM)
  · exact eight_sl_not_m2j hctx hn hnat hS h215 hL (Or.inr (Or.inl hM))
  · exact eight_sl_not_m2j hctx hn hnat hS h215 hL (Or.inr (Or.inr hM))

theorem aschbacherSixFourCore_of_tail' (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt)
    (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt) (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification)
    (hT : AschbacherSLTail') : AschbacherSixFourCore :=
  aschbacherSixFourCore_of_tail hS h215 hL (aschbacherSLTail_of_tail' hS h215 hL hT)

end Certified

end CFSG.CGT.PushingUpLit.CGT6
