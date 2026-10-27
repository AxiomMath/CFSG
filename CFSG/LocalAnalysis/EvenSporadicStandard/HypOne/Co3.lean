module

public import CFSG.Sporadic.SmallOddCore.Co3Aut
public import CFSG.Sporadic.SmallOddCore.Co3Odd
public import CFSG.Sporadic.Co3
public import Certificates.Certificate24438

public section

namespace CFSG.EvenSporadicStandard.HypOne.Co3

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore (co3Sift co3ZTbl co3TtTbl mem_co3P_of_co3Sift rep_co3ZTbl
  rep_co3TtTbl commTT_iff ctuc_co3_complete_inner_involution_classes
  ctuc_co3_involution_centralizers_odd_core_trivial co3_allInner permOK rep_tp)
open CFSG.Sporadic.Schreier.Co3 (co3P co3Z co3Tt co3M co3M1 co3M_eq_centralizer
  co3M1_eq_centralizer card_co3M card_co3M1 co3PermEquiv)

theorem fourClassesLarge_centralizerIn :
    ∀ v ∈ co3P, orderOf v = 2 → FourClassesLarge (centralizerIn co3P v) := by
  obtain ⟨fM, fM1, -⟩ := Certificates.certificate24438
  obtain ⟨-, -, -, hcl, -, -⟩ := ctuc_co3_complete_inner_involution_classes
  refine fourClassesLarge_centralizerIn_of_reps co3P [co3Z, co3Tt] (fun v hv h2 => ?_) ?_
  · by_cases h : ∃ g ∈ co3P, v = g * co3Z * g⁻¹
    · obtain ⟨g, hg, rfl⟩ := h
      exact ⟨co3Z, by simp, g, hg, rfl⟩
    · have h' : ∃ g ∈ co3P, v = g * co3Tt * g⁻¹ := by
        by_contra h''
        exact h ((hcl v hv h2).2 h'')
      obtain ⟨g, hg, rfl⟩ := h'
      exact ⟨co3Tt, by simp, g, hg, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fM
    · exact fM1

theorem center_native :
    Subgroup.center NativeSporadic.Co3 = ⊥ := by
  obtain ⟨hf, -, hs⟩ := CFSG.Sporadic.Co3.fam_co3_simplicity
  exact center_eq_bot_of_isSimpleGroup (by rw [CFSG.Sporadic.Co3.card_Co3]; norm_num)

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.Co3 :=
  hypothesisOne_of_innerModel co3PermEquiv center_native co3_allInner
    (fun v hv hv2 => ctuc_co3_involution_centralizers_odd_core_trivial v hv hv2)
    fourClassesLarge_centralizerIn

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.Co3 :=
  HasElemAbelianEight.of_mulEquiv co3PermEquiv.symm Certificates.certificate24438.2.2

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .Co3) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  exact rowData_of_hasElemAbelianEight
    (CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native)
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .Co3) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_forall_eq_conj
    (forall_eq_conj_of_mulEquiv e.symm co3_allInner)

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .Co3) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.Co3
