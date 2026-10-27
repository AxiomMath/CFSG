module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A129Native
public import CFSG.Quasithin.Background.A3Structure36B
public import CFSG.Quasithin.Background.A3StructureFactsProved
public import CFSG.Quasithin.Background.KnownMultL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.Quasithin.Background.A3Structure36AQuasi

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.SectionRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem a36BHypCat_of_mem_cComp {G : Type} [Group G] (hG : SQTKHypCat G) {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hnc : ¬ CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) :
    A36BHyp ↥L := by
  have := hG.finite
  obtain ⟨hs, hna⟩ := A36A.simple_quotient_of_mem_cComp hL
  exact
    { finite := inferInstance
      perfect := A36A.top_commutator_of_mem_cComp hL
      simple := hs
      nonabelian := hna
      o2 := hG.pCore_two_of_subnormal (subnormal_of_mem_cComp hL)
      rank := fun _ hq hq2 => isStronglyQuasithin_iff.mp (hG.subgroup L).1 _ hq hq2
      noncentral := hnc }

theorem a36StrongCat_of_not_fitting_le_center (hB : A36CaseBStatement) {G : Type} [Group G]
    (hG : SQTKHypCat G) {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G))
    (hnc : ¬ CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) : A36StrongCat L := by
  obtain ⟨h34, hcommon, hextra⟩ := hB ↥L (a36BHypCat_of_mem_cComp hG hL hnc)
  exact ⟨Or.inr (Or.inr h34), hcommon, fun _ => hextra⟩

theorem a36_quasisimple_data
    {G : Type} [Group G] (hG : SQTKHypCat G) {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hFZ : CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) :
    CFSG.IsQuasisimple ↥L ∧ CFSG.IsComponent L ∧ Odd (Nat.card (Subgroup.center ↥L)) ∧
      (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) := by
  have := hG.finite
  obtain ⟨hs, hna⟩ := A36A.simple_quotient_of_mem_cComp hL
  have hQ : CFSG.IsQuasisimple ↥L :=
    A36A.isQuasisimple_of_fitting_le_center (A36A.isPerfect_of_mem_cComp hL) hs hna hFZ
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    A36A.odd_card_center (hG.pCore_two_of_subnormal (subnormal_of_mem_cComp hL))
  exact ⟨hQ, ⟨hQ, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hL)⟩, hodd,
    (catalogStepHyp ↥L hQ (hG.subgroup L) hodd).1⟩

theorem a36CoreCat_of_fitting_le_center
    {G : Type} [Group G] (hG : SQTKHypCat G) {L : Subgroup G}
    (hL : L ∈ cComp (⊤ : Subgroup G)) (hFZ : CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) :
    A36CoreCat L := by
  have := hG.finite
  obtain ⟨hQ, hcomp, hodd, hZ13⟩ := a36_quasisimple_data hG hL hFZ
  refine ⟨Or.inl hcomp, ?_, ?_⟩
  · have hFeq : CFSG.fittingSubgroup ↥L = Subgroup.center ↥L :=
      A36A.fittingSubgroup_eq_center hFZ
    have hReq : Subgroup.center ↥L = CFSG.solvableRadical ↥L := A36A.center_eq_solvableRadical hFZ
    have hOeq : CFSG.oddCore ↥L = Subgroup.center ↥L := A36A.oddCore_eq_center hFZ hodd
    have hRR : ⁅CFSG.solvableRadical ↥L, CFSG.solvableRadical ↥L⁆ = ⊥ := by
      rw [← hReq]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hFtop : ⁅CFSG.fittingSubgroup ↥L, (⊤ : Subgroup ↥L)⁆ = ⊥ := by
      rw [hFeq]
      exact Subgroup.commutator_center_left _
    refine ⟨hFeq.trans hOeq.symm,
      (CFSG.LocalCores.quasisimple_central_quotient hQ (CFSG.fittingSubgroup ↥L) hFZ).1,
      Or.inr ⟨hFeq, hFeq.trans hReq, ?_⟩, hRR.trans hFtop.symm,
      (CFSG.LocalCores.quasisimple_central_quotient hQ
        ⁅CFSG.solvableRadical ↥L, CFSG.solvableRadical ↥L⁆ (by rw [hRR]; exact bot_le)).1⟩
    rw [hFeq]
    exact hZ13
  · intro hc
    exfalso
    have hgf : CFSG.generalizedFitting ↥L = CFSG.fittingSubgroup ↥L := by
      rcases hc with ⟨_, _, _, h, _⟩ | ⟨h, _⟩ <;> exact h
    exact A36A.generalizedFitting_ne_fittingSubgroup hQ hFZ hgf

theorem a36StrongCat_of_fitting_le_center
    (hT : ThreeCoverFactCat) {G : Type} [Group G]
    (hG : SQTKHypCat G) {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G))
    (hFZ : CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L) : A36StrongCat L := by
  have := hG.finite
  obtain ⟨hQ, hcomp, -, hZ13⟩ := a36_quasisimple_data hG hL hFZ
  have hcore := a36CoreCat_of_fitting_le_center hG hL hFZ
  have hlist : A23ListCat (↥L ⧸ Subgroup.center ↥L) := by
    have := hQ.2.1
    exact CFSG.Milestones.cl_lit_sqtk_simple_list_section G hG.isSQTKCat L
      (Subgroup.center ↥L) hQ.2.2
  refine ⟨?_, hcore.2.1, hcore.2.2⟩
  rcases hZ13 with h1 | h3
  · refine Or.inl ⟨hcomp, ?_⟩
    have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
    have := hQ.2.1
    exact ⟨e.symm.isSimpleGroup,
      CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv e.symm hlist⟩
  · exact Or.inr (Or.inl ⟨hcomp, h3, hT ↥L hQ h3 hlist⟩)

theorem a36CoreCat_of_caseB
    (hB : A36CaseBStatement) : A36CoreForSQTKCat := by
  intro _ _ hG L hL
  by_cases hnc : CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L
  · exact a36CoreCat_of_fitting_le_center hG hL hnc
  · exact (a36StrongCat_of_not_fitting_le_center hB hG hL hnc).core

theorem a36Cat_of_caseB
    (hT : ThreeCoverFactCat) (hB : A36CaseBStatement) : A36ForSQTKCat := by
  intro _ _ hG L hL
  by_cases hnc : CFSG.fittingSubgroup ↥L ≤ Subgroup.center ↥L
  · exact a36StrongCat_of_fitting_le_center hT hG hL hnc
  · exact a36StrongCat_of_not_fitting_le_center hB hG hL hnc

theorem a36ForSQTKCat_of_facts
    (h129 : A129One) (hT : ThreeCoverFactCat) : A36ForSQTKCat :=
  a36Cat_of_caseB hT (a36_caseB (A36CaseBFacts.of_proved h129 l2MultiplierFact))

theorem a36CoreForSQTKCat_of_a129
    (h129 : A129One) : A36CoreForSQTKCat :=
  a36CoreCat_of_caseB (a36_caseB (A36CaseBFacts.of_proved h129 l2MultiplierFact))

theorem a37ForSQTKCat_of_a129
    (h129 : A129One) : A37ForSQTKCat :=
  a37ForSQTKCat_of_core (a36CoreForSQTKCat_of_a129 h129)

theorem a36CoreForSQTKCat_proved
    : A36CoreForSQTKCat :=
  a36CoreForSQTKCat_of_a129 a129One

theorem a37ForSQTKCat_proved
    : A37ForSQTKCat :=
  a37ForSQTKCat_of_a129 a129One

theorem a36ForSQTKCat_of_threeCover
    (hT : ThreeCoverFactCat) : A36ForSQTKCat :=
  a36ForSQTKCat_of_facts a129One hT

theorem a37ForSQTKCat_of_facts
    (h129 : A129One) (hT : ThreeCoverFactCat) : A37ForSQTKCat :=
  a37ForSQTKCat_of_a36 (a36ForSQTKCat_of_facts h129 hT)

end CFSG.QuasithinUnique.Vol2Native
