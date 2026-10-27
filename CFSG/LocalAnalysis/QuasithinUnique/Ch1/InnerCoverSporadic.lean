module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique CFSG.Milestones

theorem invCaseF_of_sporadic
    (hS : SporadicAutInner) {K : Type} [Group K] [Finite K] {β : K ≃* K}
    (h : InvDatum K β) (hz : Subgroup.center K = ⊥) (hK : SporadicList K) : InvCaseF K β := by
  obtain ⟨s, hs, ⟨e⟩⟩ := hK
  by_cases hs1 : s = .J1
  · exfalso
    subst hs1
    obtain ⟨l, hl⟩ := isInnerAut_of_carrierJ1 e β
    obtain ⟨hl1, hll⟩ := h.involution_of_inner hz hl
    exact j1_involution_centralizer K ⟨e⟩ l hl1 hll
      (by rw [← fixedSubgroup_eq_centralizer hl]; exact h.charTwo)
  · have hβ : IsInnerAut β := hS s hs hs1 K ⟨e⟩ β h.involutory h.sylow
    have hs' : IsLemma115SporadicName s := by
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hs1 | simp [IsLemma115SporadicName]
    have hpc : CFSG.pCore 2 K = ⊥ := h.pCore_eq_bot hz
    let e' : (K ⧸ CFSG.pCore 2 K) ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    exact ⟨⟨s, hs', ⟨e'.trans e⟩⟩, h.isTwoCentralInnerAut_of_inner hβ⟩

theorem InvDatum.invCases_of_quotient_caseF {L : Type} [Group L] [Finite L] {α : L ≃* L}
    (h : InvDatum L α) (hKF : InvCaseF (L ⧸ Subgroup.center L) (quotAut α)) : InvCases L α := by
  have hKc : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := center_quotient_eq_bot h.quasisimple
  obtain ⟨⟨s, hs, ⟨e'⟩⟩, hβ⟩ := hKF
  have hi : IsInnerAut α := h.isInnerAut_of_quotAut_inner (by
    obtain ⟨l, hl, -⟩ := hβ
    exact ⟨l, hl⟩)
  have hpc := h.pCore_eq_center_of_inner hi
  have hpcK : CFSG.pCore 2 (L ⧸ Subgroup.center L) = ⊥ := by
    rw [pCore_eq_center_of_isPGroup_center (isQuasisimple_quotient h.quasisimple)
      (by rw [hKc]; exact IsPGroup.of_bot), hKc]
  let eK : (L ⧸ CFSG.pCore 2 L) ≃* (L ⧸ Subgroup.center L) :=
    QuotientGroup.quotientMulEquivOfEq hpc
  let eK' : (L ⧸ Subgroup.center L) ≃* (L ⧸ Subgroup.center L) ⧸
      CFSG.pCore 2 (L ⧸ Subgroup.center L) :=
    (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hpcK.symm)
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨s, hs, ⟨(eK.trans eK').trans e'⟩⟩,
    h.isTwoCentralInnerAut_of_inner hi⟩))))

theorem simpleInspection_nonSporadic (hAlt : SimpleInspection AltList)
    (hOdd : SimpleInspection OddList) (hEven : SimpleInspection SQTKCharTwoLie) :
    SimpleInspection NonSporadicList := by
  intro K _ _ β h hz hK
  rcases hK with hK | hK | hK
  · exact hAlt K β h hz hK
  · exact hOdd K β h hz hK
  · exact hEven K β h hz hK

theorem invCases_of_inspections_nonSporadic (hS : SimpleInspection NonSporadicList)
    (hF : ∀ (K : Type) [Group K] [Finite K] (β : K ≃* K), InvDatum K β →
      Subgroup.center K = ⊥ → SporadicList K → InvCaseF K β)
    (hI : InnerCover NonSporadicList) (hA : AltOuterCover) {L : Type} [Group L] [Finite L]
    {α : L ≃* L} (h : InvDatum L α) (hP : SQTKSimpleList (L ⧸ Subgroup.center L)) :
    InvCases L α := by
  rcases (sqtkSimpleList_iff _).mp hP with hP | hP | hP | hP
  · exact invCases_of_inspections hS hI hA h (Or.inl hP)
  · exact invCases_of_inspections hS hI hA h (Or.inr (Or.inl hP))
  · exact invCases_of_inspections hS hI hA h (Or.inr (Or.inr hP))
  · exact h.invCases_of_quotient_caseF
      (hF _ (quotAut α) h.quotient (center_quotient_eq_bot h.quasisimple) hP)

end CFSG.QuasithinUnique.Ch1

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Ch1 CFSG.Milestones

theorem lemma115_3_List_of_nonSporadic_inspections
    (hS : SimpleInspection NonSporadicList)
    (hF : ∀ (K : Type) [Group K] [Finite K] (β : K ≃* K), InvDatum K β →
      Subgroup.center K = ⊥ → SporadicList K → InvCaseF K β)
    (hI : InnerCover NonSporadicList) (hA : AltOuterCover) : Lemma115_3_List := by
  intro G _ _ _ _ hqtke H S M z h L hL
  obtain ⟨α, hα, hdatum⟩ := lemma115_exists_invDatum h hL
  exact Lemma115Cases.of_invCases hα
    (invCases_of_inspections_nonSporadic hS hF hI hA hdatum
      (sqtkSimpleList_component hqtke.1 h.pCore_ne_bot hL))

end CFSG.QuasithinUnique
