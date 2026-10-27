module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporFive

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows

section Fi22

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.RankThree.Native CFSG.Monster.B.Fischer


theorem crow_Fi22_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    CRow .Fi22 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, hQsyl⟩, ⟨hlinesSet, -⟩, -, hrec⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  have e : CFSG.Blueprint.NativeSporadic.Fi22 ≃* ↥fi22P := fi22PermEquiv
  have hfin : Finite ↥fi22P := inferInstance
  have hs : IsSimpleGroup ↥fi22P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e.symm
  have hc : Nat.card ↥fi22P = 64561751654400 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Fi22.card_Fi22
  have hpr : ¬ (Nat.card ↥fi22P).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥fi22P, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥fi22P _ hfin hs hpr
  have b : ↥fi22P ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group := e.symm.trans (hbr .Fi22).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ i, Subgroup.zpowers (fi22FiveLine i) ≤ fi22FiveQ ∧
      Nat.card (Subgroup.zpowers (fi22FiveLine i)) = 5 := by
    intro i
    have h : Subgroup.zpowers (fi22FiveLine i) ∈
        {H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨i, rfl⟩
    exact h
  have hmem : ∀ i, fi22FiveLine i ∈ fi22P :=
    fun i => hQP ((hlineQ i).1 (Subgroup.mem_zpowers _))
  have hline : ∀ i, CCompOK 5 (⟨fi22FiveLine i, hmem i⟩ : ↥fi22P) := by
    intro i
    obtain ⟨-, -, hCP, -, hDP, hDs, hDnab, hDcard, -, -, -, -, -, hcentP⟩ := hrec i
    have hDCi : fi22FiveD i ≤ fi22FiveC i := commutator_self_le' _
    have hDC : fi22FiveD i ≤ fi22FiveC i ⊓ fi22P := le_inf hDCi hDP
    have hDn : ((fi22FiveD i).subgroupOf (fi22FiveC i ⊓ fi22P)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := commutator_self_conj_mem (Subgroup.mem_inf.1 g.2).1 hn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact h
    have hDfin : Finite ↥(fi22FiveD i) := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    exact ccompOK_of_normal_record Nat.prime_five le_rfl (hmem i) hCP hDC hDn hDs hDnab hDP
      hcentP (orderOf_fi22FiveLine i) (gLAPPrimeCoreOf_fi22FiveLine_eq_bot i)
      (by rw [hDcard]; norm_num) (ctypeOK_A5 (Or.inr rfl)
        (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some)
  exact @crow_of_model .Fi22 5 ↥fi22P _ hfin hs hOut b hnc
    (@ccompOK_of_lines 3510 5 Nat.prime_five fi22P fi22FiveQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ fi22FiveLine hlines hmem hline)

end Fi22


section Suz

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore


theorem crow_Suz_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hb : LieOrderBridge) : CRow .Suz 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, -, hQsyl⟩, ⟨hlinesSet, -⟩, hrec, hgood, hbad⟩ :=
    R3E_Suz_full_five_centralizer_structures
  have hR : ∀ r ∈ suzT, ∀ q ∈ suzM, r * q * r⁻¹ ∈ suzM := fun r hr q hq =>
    suzT_conj_mem_suzM hr hq
  have e : CFSG.Blueprint.NativeSporadic.Suz ≃* ↥suzM := suzEquivM
  have hfin : Finite ↥suzM := inferInstance
  have hs : IsSimpleGroup ↥suzM :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e.symm
  have hc : Nat.card ↥suzM = 448345497600 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Suz.card_Suz
  have hpr : ¬ (Nat.card ↥suzM).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥suzM, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥suzM _ hfin hs hpr
  have b : ↥suzM ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group := e.symm.trans (hbr .Suz).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ i, Subgroup.zpowers (suzFiveLine i) ≤ suzFiveQ ∧
      Nat.card (Subgroup.zpowers (suzFiveLine i)) = 5 := by
    intro i
    have h : Subgroup.zpowers (suzFiveLine i) ∈
        {H : Subgroup (Equiv.Perm (Fin 1782)) | H ≤ suzFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨i, rfl⟩
    exact h
  have hmem : ∀ i, suzFiveLine i ∈ suzM :=
    fun i => hQP ((hlineQ i).1 (Subgroup.mem_zpowers _))
  have hord : ∀ i, orderOf (suzFiveLine i) = 5 := fun i => by
    rw [← Nat.card_zpowers]; exact (hlineQ i).2
  have hline : ∀ i, CCompOK 5 (⟨suzFiveLine i, hmem i⟩ : ↥suzM) := by
    intro i
    obtain ⟨hCeq, hDs, hDnab, hDM⟩ := hrec i
    have hD : (⁅suzFiveC i, suzFiveC i⁆ : Subgroup (Equiv.Perm (Fin 1782))) = suzFiveD i := rfl
    by_cases hg : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
    · obtain ⟨-, hDcard, hcentEq, hcard5⟩ := hgood i hg
      have hDC : suzFiveD i ≤ suzFiveC i := hD ▸ commutator_self_le' _
      have hDn : ((suzFiveD i).subgroupOf (suzFiveC i)).Normal := by
        refine ⟨fun n hn g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have h := commutator_self_conj_mem g.2 (hD ▸ hn)
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hD ▸ h
      have hcore : GLAPPrimeCoreOf 5
          (Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓ suzT) = ⊥ := by
        rw [← hCeq]
        exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
          (by rw [hD, hDcard]; norm_num)
          (IsPGroup.of_card (n := 1) (by rw [pow_one, hD, hcentEq]; exact hcard5))
      have hDfin : Finite ↥(suzFiveD i) := Finite.of_injective (Subgroup.inclusion hDM)
        (Subgroup.inclusion_injective hDM)
      exact ccompOK_of_normal_record Nat.prime_five suzM_le_suzT (hmem i) hCeq hDC hDn hDs hDnab
        hDM hcentEq (hord i)
        (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five suzM_le_suzT hR hcore)
        (by rw [hDcard]; norm_num) (ctypeOK_five_of_card_360 hb hDcard)
    · have hb' : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
        have := i.2
        omega
      obtain ⟨hCcard, -, -⟩ := hbad i hb'
      refine ccompOK_five_of_card_dvd_3000 ?_
      have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype suzM
        (⟨suzFiveLine i, hmem i⟩ : ↥suzM)
      have hcc : Nat.card (Subgroup.centralizer ({(⟨suzFiveLine i, hmem i⟩ : ↥suzM)} : Set ↥suzM)) =
          Nat.card ↥(Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓
            suzM) := by
        rw [← hmapc, Subgroup.card_map_of_injective suzM.subtype_injective]
      rw [hcc]
      have hle : Subgroup.centralizer ({suzFiveLine i} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM ≤
          suzFiveC i := by
        rw [hCeq]
        exact inf_le_inf_left _ suzM_le_suzT
      exact (Subgroup.card_dvd_of_le hle).trans (by rw [hCcard]; norm_num)
  exact @crow_of_model .Suz 5 ↥suzM _ hfin hs hOut b hnc
    (@ccompOK_of_lines 1782 5 Nat.prime_five suzM suzFiveQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ suzFiveLine hlines hmem hline)

end Suz

end CFSG.LocalAnalysis.GLTheoremA.Chev2Rows
