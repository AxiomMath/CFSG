module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRowsA

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1415Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows
open scoped commutatorElement

section Co3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3

theorem arow_Co3_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    I1415Row .Co3 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrec0, hrec25, hC0, -, hDs, hDnab, hDcard,
    hDcent, -, hC25, -, hAC, hAn, hAcard, -, -, hAc⟩ := R3E_Co3_full_five_centralizer_structures
  have e : CFSG.Blueprint.NativeSporadic.Co3 ≃* ↥co3P := co3PermEquiv
  have hfin : Finite ↥co3P := inferInstance
  have hs : IsSimpleGroup ↥co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  have hc : Nat.card ↥co3P = 495766656000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Co3.card_Co3
  have hpr : ¬ (Nat.card ↥co3P).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥co3P, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥co3P _ hfin hs hpr
  have b : ↥co3P ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group := e.symm.trans (hbr .Co3).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (co3FiveLine j) ≤ co3FiveQ ∧
      Nat.card (Subgroup.zpowers (co3FiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (co3FiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 276)) | H ≤ co3FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, co3FiveLine j ∈ co3P :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (co3FiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hnorm : ∀ r ∈ co3P, ∀ q ∈ co3P, r * q * r⁻¹ ∈ co3P :=
    fun r hr q hq => co3P.mul_mem (co3P.mul_mem hr hq) (co3P.inv_mem hr)
  have hL0 : ACompOK 5 (⟨co3FiveLine 0, hmem 0⟩ : ↥co3P) := by
    have hD : co3FiveD = ⁅co3FiveC0, co3FiveC0⁆ := rfl
    have hDC : co3FiveD ≤ co3FiveC0 := by
      rw [hD, Subgroup.commutator_le]
      intro a ha c hc
      rw [commutatorElement_def]
      exact co3FiveC0.mul_mem (co3FiveC0.mul_mem (co3FiveC0.mul_mem ha hc)
        (co3FiveC0.inv_mem ha)) (co3FiveC0.inv_mem hc)
    have hDP : co3FiveD ≤ co3P := fun d hd => (hC0 ▸ hDC hd : d ∈ _ ⊓ co3P).2
    have hDfin : Finite ↥co3FiveD := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    exact acompOK_of_derived_record (C := co3FiveC0) (D := co3FiveD) Nat.prime_five le_rfl
      (hmem 0) hC0 hD hDs hDnab hDP hDcent (hord 0)
      (gLAPPrimeCoreOf_co3FiveRecord_eq_bot 0 (Or.inl rfl)) (by rw [hDcard]; norm_num)
      (atypeOK_A5 (Or.inr rfl)
        (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some)
  have hL25 : ACompOK 5 (⟨co3FiveLine 25, hmem 25⟩ : ↥co3P) := by
    have hAP : co3FiveA ≤ co3P := fun a ha => (hC25 ▸ hAC ha : a ∈ _ ⊓ co3P).2
    exact acompOK_of_pgroup_record Nat.prime_five le_rfl (hmem 25) hC25 hAC hAn hAP
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hline : ∀ j, ACompOK 5 (⟨co3FiveLine j, hmem j⟩ : ↥co3P) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : ACompOK 5 (⟨co3FiveLine (co3FiveRecordOf j), hmem _⟩ : ↥co3P) := by
      by_cases h : (j : ℕ) = 25
      · rw [(hrec25 j).2 h]; exact hL25
      · rw [(hrec0 j).2 h]; exact hL0
    have h := acompOK_conj Nat.prime_five hnorm hjP (hmem _) hr
    have heq : (⟨co3FiveTransporter j * co3FiveLine (co3FiveRecordOf j) *
        (co3FiveTransporter j)⁻¹, hnorm _ hjP _ (hmem _)⟩ : ↥co3P) =
        ⟨co3FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @arow_of_model .Co3 5 ↥co3P _ hfin hs hOut b hnc
    (@acompOK_of_lines 276 5 Nat.prime_five co3P co3FiveQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ co3FiveLine hlines hmem hline)

end Co3

section Co2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.Co2Cert

theorem arow_Co2_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    I1415Row .Co2 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrec0, hC0, -, hAC, hAn, hAcard, -, -,
    hAc, hC1, -, hDs, hDnab, hDcard, hDcent, hDcard5⟩ := R3E_Co2_full_five_centralizer_structures
  have e : CFSG.Blueprint.NativeSporadic.Co2 ≃* ↥co2P := co2PermEquiv
  have hfin : Finite ↥co2P := inferInstance
  have hs : IsSimpleGroup ↥co2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 e.symm
  have hc : Nat.card ↥co2P = 42305421312000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Co2.card_Co2
  have hpr : ¬ (Nat.card ↥co2P).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥co2P, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥co2P _ hfin hs hpr
  have b : ↥co2P ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group := e.symm.trans (hbr .Co2).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (co2FiveLine j) ≤ co2FiveQ ∧
      Nat.card (Subgroup.zpowers (co2FiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (co2FiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 2300)) | H ≤ co2FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, co2FiveLine j ∈ co2P :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (co2FiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hnorm : ∀ r ∈ co2P, ∀ q ∈ co2P, r * q * r⁻¹ ∈ co2P :=
    fun r hr q hq => co2P.mul_mem (co2P.mul_mem hr hq) (co2P.inv_mem hr)
  have hL0 : ACompOK 5 (⟨co2FiveLine 0, hmem 0⟩ : ↥co2P) := by
    have hAP : co2FiveA ≤ co2P := fun a ha => (hC0 ▸ hAC ha : a ∈ _ ⊓ co2P).2
    exact acompOK_of_pgroup_record Nat.prime_five le_rfl (hmem 0) hC0 hAC hAn hAP
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hL1 : ACompOK 5 (⟨co2FiveLine 1, hmem 1⟩ : ↥co2P) := by
    have hD : co2FiveD = ⁅co2FiveC1, co2FiveC1⁆ := rfl
    have hDC : co2FiveD ≤ co2FiveC1 := by
      rw [hD, Subgroup.commutator_le]
      intro a ha c hc
      rw [commutatorElement_def]
      exact co2FiveC1.mul_mem (co2FiveC1.mul_mem (co2FiveC1.mul_mem ha hc)
        (co2FiveC1.inv_mem ha)) (co2FiveC1.inv_mem hc)
    have hDP : co2FiveD ≤ co2P := fun d hd => (hC1 ▸ hDC hd : d ∈ _ ⊓ co2P).2
    have hDfin : Finite ↥co2FiveD := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    have hcore : GLAPPrimeCoreOf 5
        (Subgroup.centralizer ({co2FiveLine 1} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) = ⊥ := by
      rw [← hC1]
      exact gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five hDs hDnab
        (by rw [← hD, hDcard]; norm_num)
        (IsPGroup.of_card (n := 1) (by rw [pow_one, ← hD]; exact hDcard5))
    exact acompOK_of_derived_record (C := co2FiveC1) (D := co2FiveD) Nat.prime_five le_rfl
      (hmem 1) hC1 hD hDs hDnab hDP hDcent (hord 1) hcore (by rw [hDcard]; norm_num)
      (atypeOK_A5 (Or.inr rfl)
        (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some)
  have hline : ∀ j, ACompOK 5 (⟨co2FiveLine j, hmem j⟩ : ↥co2P) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : ACompOK 5 (⟨co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)), hmem _⟩ : ↥co2P) := by
      by_cases h : (j : ℕ) = 0
      · rw [(hrec0 j).2 h]; exact hL0
      · have h1 : co2FiveRecordOf j = 1 := by
          simp only [co2FiveRecordOf, h, if_false]
        rw [h1]; exact hL1
    have h := acompOK_conj Nat.prime_five hnorm hjP (hmem _) hr
    have heq : (⟨co2FiveTransporter j * co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) *
        (co2FiveTransporter j)⁻¹, hnorm _ hjP _ (hmem _)⟩ : ↥co2P) =
        ⟨co2FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @arow_of_model .Co2 5 ↥co2P _ hfin hs hOut b hnc
    (@acompOK_of_lines 2300 5 Nat.prime_five co2P co2FiveQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ co2FiveLine hlines hmem hline)

end Co2

end CFSG.LocalAnalysis.GLTheoremA.I1415Rows
