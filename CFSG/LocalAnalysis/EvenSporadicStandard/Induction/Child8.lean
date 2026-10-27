module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic

theorem center_eq_bot_of_stdHyp {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    {s : TauCeti.SporadicName} (hsimp : IsSimpleGroup (Carrier s)) (hL : IsSporadic ↥L s) :
    center ↥L = ⊥ := by
  obtain ⟨e⟩ := hL
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.2 h.standard.1
  have : Nontrivial ↥L := e.toEquiv.nontrivial
  have : IsSimpleGroup ↥L :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥L) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).1.1 hq
    have h1 : ∀ x : ↥L ⧸ center ↥L, x = 1 := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      exact (QuotientGroup.eq_one_iff y).2 (hc ▸ mem_top y)
    exact hab (by rw [h1 a, h1 b])

theorem sol78Concl_of_stdHyp {S : List TauCeti.SporadicName} {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hpred : Sol78PredS S G) (h : StdHyp G L) {s : TauCeti.SporadicName}
    (hs : s ∈ S) (hsimp : IsSimpleGroup (Carrier s)) (hL : IsSporadic ↥L s) :
    IsSporadic ↥L .Fi23 ∧ IsSporadic G .Fi24Prime := by
  have hc := center_eq_bot_of_stdHyp h hsimp hL
  have hq : CFSG.IsQuasisimple ↥L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥L).2.2.1.2 h.standard.1
  have hcov : OddCover s L := by
    obtain ⟨e⟩ := hL
    refine ⟨hq, ?_, ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans
      QuotientGroup.quotientBot).trans e⟩⟩
    rw [hc, Subgroup.card_bot]
    exact odd_one
  obtain ⟨h23, ⟨e24⟩⟩ :=
    hpred ⊤ h.fStarSimple h.index_top_le_two h.kProper L h.solStd ⟨s, hs, hcov⟩
  exact ⟨h23, ⟨Subgroup.topEquiv.symm.trans e24⟩⟩

theorem not_isSporadic_of_sol78PredS {S : List TauCeti.SporadicName} {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hpred : Sol78PredS S G) (h : StdHyp G L)
    {s : TauCeti.SporadicName} (hs : s ∈ S) (hsimp : IsSimpleGroup (Carrier s))
    (hne : Nat.card (Carrier s) ≠ Nat.card (Carrier .Fi23)) : ¬ IsSporadic ↥L s := by
  intro hL
  obtain ⟨⟨e23⟩, -⟩ := sol78Concl_of_stdHyp hpred h hs hsimp hL
  obtain ⟨e⟩ := hL
  exact hne ((Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e23.toEquiv))

theorem not_isSporadic_fi23_of_sol78PredS {S : List TauCeti.SporadicName} {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hpred : Sol78PredS S G) (h : StdHyp G L) (hs : .Fi23 ∈ S)
    (hsimp : IsSimpleGroup (Carrier .Fi23)) (hsc : Fi.V3.Fi23SelfCentralizing) :
    ¬ IsSporadic ↥L .Fi23 := by
  intro hL
  obtain ⟨-, ⟨e24⟩⟩ := sol78Concl_of_stdHyp hpred h hs hsimp hL
  have hcL := center_eq_bot_of_stdHyp h hsimp hL
  have hF := h.fStarSimple
  have hcT : center ↥(⊤ : Subgroup G) = ⊥ := by
    have := hF.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥(⊤ : Subgroup G)) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨a, b, hab⟩ := hF.nonabelian
      exact hab (mem_center_iff.1 (hc ▸ mem_top b) a)
  have hcovT : OddCover .Fi24Prime (⊤ : Subgroup G) := by
    refine ⟨hF.isQuasisimple, ?_, ⟨((QuotientGroup.quotientMulEquivOfEq hcT).trans
      QuotientGroup.quotientBot).trans (Subgroup.topEquiv.trans e24)⟩⟩
    rw [hcT, Subgroup.card_bot]
    exact odd_one
  obtain ⟨t, ht2, hcomp⟩ := h.solStd.exists_involution
  have hKs : IsSporadic (↥L ⧸ center ↥L) .Fi23 := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hcL).trans QuotientGroup.quotientBot).trans e⟩
  have hcomm := hsc G ⊤ L hcovT le_top hcomp.isQuasisimple hKs t (mem_top t)
    (fun k hk => mem_centralizer_singleton_iff.1 (hcomp.le hk))
  have htc : (⟨t, mem_top t⟩ : ↥(⊤ : Subgroup G)) ∈ center ↥(⊤ : Subgroup G) :=
    mem_center_iff.2 fun g => Subtype.ext (hcomm g.1 g.2)
  rw [hcT, mem_bot] at htc
  have ht1 : t = 1 := congrArg Subtype.val htc
  rw [ht1, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

end CFSG.EvenSporadicStandard.Induction
