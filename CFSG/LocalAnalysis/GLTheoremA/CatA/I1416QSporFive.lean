module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRowsA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAutSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416QRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows
open scoped commutatorElement

theorem qcompOK_of_normal_record {n p : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))} (hp : p.Prime)
    (hPR : P ≤ R) {x : Equiv.Perm (Fin n)}
    (hxP : x ∈ P) {C D : Subgroup (Equiv.Perm (Fin n))}
    (hC : C = Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ R) (hDC : D ≤ C)
    (hDn : (D.subgroupOf C).Normal)
    (hDs : IsSimpleGroup ↥D) (hDnab : ∃ g ∈ D, ∃ h ∈ D, g * h ≠ h * g) (hDP : D ≤ P)
    (hDcent : Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C = Subgroup.zpowers x)
    (hxo : orderOf x = p)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) = ⊥)
    (hpD : p ∣ Nat.card ↥D) (hT : QTypeOK p ↥D) : QCompOK p (⟨x, hxP⟩ : ↥P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k : ↥P := ⟨x, hxP⟩ with hk
  set Cq : Subgroup ↥P := Subgroup.centralizer ({k} : Set ↥P) with hCq
  set L : Subgroup ↥P := D.subgroupOf P with hL
  let eL : ↥L ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDP
  haveI hLs : IsSimpleGroup ↥L := (MulEquiv.isSimpleGroup_congr eL).2 hDs
  have hLnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨g, hg, h, hh, hgh⟩ := hDnab
    refine ⟨eL.symm ⟨g, hg⟩, eL.symm ⟨h, hh⟩, fun he => hgh ?_⟩
    have := congrArg (fun z => ((eL z : ↥D) : Equiv.Perm (Fin n))) he
    simpa using this
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.HardMathSupport.Dickson.I271.isQuasisimpleOpen_of_simple_nonab hLnab
  have hxcent : x ∈ Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) := by
    have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [← hDcent] at this
    exact this.1
  have hgC : ∀ g : ↥P, g ∈ Cq → (g : Equiv.Perm (Fin n)) ∈ C := by
    intro g hg
    rw [hC]
    refine Subgroup.mem_inf.2 ⟨?_, hPR g.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact congrArg Subtype.val hg
  have hLC : L ≤ Cq := by
    intro l hl
    rw [hCq, Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 hxcent _ (Subgroup.mem_subgroupOf.1 hl))
  have hLn : ∀ g ∈ Cq, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    rw [hL, Subgroup.mem_subgroupOf] at hl ⊢
    have h2 := hDn.conj_mem ⟨(l : Equiv.Perm (Fin n)), hDC hl⟩ (Subgroup.mem_subgroupOf.2 hl)
      ⟨(g : Equiv.Perm (Fin n)), hgC g hg⟩
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hcoreQ : GLAPPrimeCore p ↥Cq = ⊥ := by
    let e1 : ↥Cq ≃* ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) :=
      (Cq.equivMapOfInjective P.subtype P.subtype_injective).trans
        (MulEquiv.subgroupCongr (CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype' P k))
    have h0 := (CFSG.HardMathSupport.Dickson.I271.glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore p _).1
      hcore
    rw [← glaPPrimeCore_map_iso p e1.symm, h0, Subgroup.map_bot]
  have hcent : IsPGroup p ↥(Cq ⊓ Subgroup.centralizer (L : Set ↥P)) := by
    intro c
    refine ⟨1, ?_⟩
    have hcD : ((c : ↥P) : Equiv.Perm (Fin n)) ∈
        Subgroup.centralizer (D : Set (Equiv.Perm (Fin n))) ⊓ C := by
      refine ⟨Subgroup.mem_centralizer_iff.2 fun d hd => ?_, hgC _ c.2.1⟩
      have h := Subgroup.mem_centralizer_iff.1 c.2.2 ⟨d, hDP hd⟩ (Subgroup.mem_subgroupOf.2 hd)
      exact congrArg Subtype.val h
    rw [hDcent] at hcD
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hcD
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_pow, pow_one, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo,
      pow_orderOf_eq_one, one_zpow]
  have hcoreL : GLAPPrimeCore p ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥L) with h | h
    · exact h
    · exfalso
      have hcop := GL83.PiGen.coprime_card_glaPPrimeCore hp ↥L
      rw [h, Subgroup.card_top, Nat.card_congr eL.toEquiv] at hcop
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpD
  have hZL : Subgroup.center ↥L = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hLnab
  intro I hI
  have hIL : I = L :=
    CFSG.HardMathSupport.Dickson.I271.eq_of_glaPComponent_of_normal_quasisimple hp hLC hLn hLq
      hcoreQ hcent hI
  rw [hIL]
  exact (hT.of_mulEquiv eL.symm).of_mulEquiv
    (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf L hcoreL hZL).symm

section J2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore


theorem qrow_J2_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    I1416QRow .J2 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, hQcard, -⟩, ⟨hlinesSet, -⟩, hrec, hgood, hbad⟩ :=
    R3E_J2_full_five_centralizer_structure
  have hM := j2_autModel
  have e : CFSG.Blueprint.NativeSporadic.J2 ≃* ↥j2P := j2PermEquiv
  have hfin : Finite ↥j2P := inferInstance
  have hs : IsSimpleGroup ↥j2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e.symm
  have hc : Nat.card ↥j2P = 604800 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.J2.card_J2
  have hpr : ¬ (Nat.card ↥j2P).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥j2P, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥j2P _ hfin hs hpr
  have b : ↥j2P ≃* (TauCeti.CFSGIndex.sporadic .J2).Group := e.symm.trans (hbr .J2).some
  have hlineQ : ∀ i, Subgroup.zpowers (j2FiveLine i) ≤ j2FiveQ ∧
      Nat.card (Subgroup.zpowers (j2FiveLine i)) = 5 := by
    intro i
    have h : Subgroup.zpowers (j2FiveLine i) ∈
        {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨i, rfl⟩
    exact h
  have hmem : ∀ i, j2FiveLine i ∈ j2P :=
    fun i => hQP ((hlineQ i).1 (Subgroup.mem_zpowers _))
  have hline : ∀ i, QCompOK 5 (⟨j2FiveLine i, hmem i⟩ : ↥j2P) := by
    intro i
    obtain ⟨hCeq, hQC, hQeq, -⟩ := hrec i
    have hC : j2FiveC i =
        Subgroup.centralizer ({j2FiveLine i} : Set (Equiv.Perm (Fin 315))) ⊓ j2R := by
      rw [hCeq, inf_comm]
    by_cases hg : i.val = 0 ∨ i.val = 1 ∨ i.val = 4
    · obtain ⟨-, hnorm⟩ := hgood i hg
      exact qcompOK_of_pgroup_record Nat.prime_five hM.le (hmem i) hC hQC hnorm hQP
        j2FiveQ_isPGroup (le_of_eq hQeq)
    · have hbad' : i.val = 2 ∨ i.val = 3 ∨ i.val = 5 := by
        have := i.2
        omega
      obtain ⟨-, hDP, hDs, hDnab, hDcard, hDn, hDcent, -⟩ := hbad i hbad'
      obtain ⟨-, hDC, -⟩ := (j2Five_record i).2.2 hbad'
      have hDfin : Finite ↥(j2FiveD i) := Finite.of_injective (Subgroup.inclusion hDP)
        (Subgroup.inclusion_injective hDP)
      refine qcompOK_of_normal_record Nat.prime_five hM.le (hmem i) hC hDC hDn hDs hDnab hDP
        hDcent (orderOf_j2FiveLine i) ?_ (by rw [hDcard]; norm_num) (qtypeOK_A5 (Or.inr rfl)
          (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
            hDfin hDs hDcard).some)
      exact gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
        (gLAPPrimeCoreOf_j2FiveC_eq_bot i)
  exact @qrow_of_model .J2 5 ↥j2P _ hfin hs hOut b hnc
    (@qcompOK_of_lines 315 5 Nat.prime_five j2P j2FiveQ hQP
      (by rw [hQcard, factorization_card_j2P_five]; norm_num) _ j2FiveLine
      (fun H hHQ hHc => by
        have hm : H ∈ {H : Subgroup (Equiv.Perm (Fin 315)) | H ≤ j2FiveQ ∧ Nat.card H = 5} :=
          ⟨hHQ, hHc⟩
        rw [hlinesSet] at hm
        obtain ⟨j, hj⟩ := hm
        exact ⟨j, hj.symm⟩) hmem hline)

end J2

section Co3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3


theorem qrow_Co3_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    I1416QRow .Co3 5 := by
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
  have hL0 : QCompOK 5 (⟨co3FiveLine 0, hmem 0⟩ : ↥co3P) := by
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
    exact qcompOK_of_derived_record (C := co3FiveC0) (D := co3FiveD) Nat.prime_five le_rfl
      (hmem 0) hC0 hD hDs hDnab hDP hDcent (hord 0)
      (gLAPPrimeCoreOf_co3FiveRecord_eq_bot 0 (Or.inl rfl)) (by rw [hDcard]; norm_num)
      (qtypeOK_A5 (Or.inr rfl)
        (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some)
  have hL25 : QCompOK 5 (⟨co3FiveLine 25, hmem 25⟩ : ↥co3P) := by
    have hAP : co3FiveA ≤ co3P := fun a ha => (hC25 ▸ hAC ha : a ∈ _ ⊓ co3P).2
    exact qcompOK_of_pgroup_record Nat.prime_five le_rfl (hmem 25) hC25 hAC hAn hAP
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hline : ∀ j, QCompOK 5 (⟨co3FiveLine j, hmem j⟩ : ↥co3P) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : QCompOK 5 (⟨co3FiveLine (co3FiveRecordOf j), hmem _⟩ : ↥co3P) := by
      by_cases h : (j : ℕ) = 25
      · rw [(hrec25 j).2 h]; exact hL25
      · rw [(hrec0 j).2 h]; exact hL0
    have h := qcompOK_conj Nat.prime_five hnorm hjP (hmem _) hr
    have heq : (⟨co3FiveTransporter j * co3FiveLine (co3FiveRecordOf j) *
        (co3FiveTransporter j)⁻¹, hnorm _ hjP _ (hmem _)⟩ : ↥co3P) =
        ⟨co3FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @qrow_of_model .Co3 5 ↥co3P _ hfin hs hOut b hnc
    (@qcompOK_of_lines 276 5 Nat.prime_five co3P co3FiveQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ co3FiveLine hlines hmem hline)

end Co3

section He

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.HeldB


theorem qrow_He_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    I1416QRow .He 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrec, ⟨hC0, -⟩,
    ⟨hDs, hDnab, hDcard, hDP, hDcent, -⟩⟩ := R3E_He_full_five_centralizer_structures
  have hM := heAutModel
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥heP := heEquivP
  have hfin : Finite ↥heP := inferInstance
  have hs : IsSimpleGroup ↥heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  have hc : Nat.card ↥heP = 4030387200 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.He.card_He
  have hpr : ¬ (Nat.card ↥heP).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥heP, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥heP _ hfin hs hpr
  have b : ↥heP ≃* (TauCeti.CFSGIndex.sporadic .He).Group := e.symm.trans (hbr .He).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (heFiveLine j) ≤ heFiveQ ∧
      Nat.card (Subgroup.zpowers (heFiveLine j)) = 5 := by
    intro j
    have h : Subgroup.zpowers (heFiveLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heFiveQ ∧ Nat.card H = 5} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, heFiveLine j ∈ heP :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (heFiveLine j) = 5 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hL0 : QCompOK 5 (⟨heFiveLine 0, hmem 0⟩ : ↥heP) := by
    have hDfin : Finite ↥heFiveD0 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    exact qcompOK_of_derived_record (C := heFiveC0) (D := heFiveD0) Nat.prime_five hM.le
      (hmem 0) hC0 rfl hDs hDnab hDP hDcent (hord 0)
      (gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le hM.conj_mem
        gLAPPrimeCoreOf_heFiveRecord_eq_bot) (by rw [hDcard]; norm_num)
      (qtypeOK_A5 (Or.inr rfl)
        (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some)
  have hline : ∀ j, QCompOK 5 (⟨heFiveLine j, hmem j⟩ : ↥heP) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : QCompOK 5 (⟨heFiveLine (heFiveRecordOf j), hmem _⟩ : ↥heP) := by
      rw [hrec j]; exact hL0
    have h := qcompOK_conj Nat.prime_five hM.conj_mem hjR (hmem _) hr
    have heq : (⟨heFiveTransporter j * heFiveLine (heFiveRecordOf j) *
        (heFiveTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥heP) =
        ⟨heFiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @qrow_of_model .He 5 ↥heP _ hfin hs hOut b hnc
    (@qcompOK_of_lines 8330 5 Nat.prime_five heP heFiveQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ heFiveLine hlines hmem hline)

end He

section Co2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.Native CFSG.Sporadic.Co2Cert


theorem qrow_Co2_five (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    I1416QRow .Co2 5 := by
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
  have hL0 : QCompOK 5 (⟨co2FiveLine 0, hmem 0⟩ : ↥co2P) := by
    have hAP : co2FiveA ≤ co2P := fun a ha => (hC0 ▸ hAC ha : a ∈ _ ⊓ co2P).2
    exact qcompOK_of_pgroup_record Nat.prime_five le_rfl (hmem 0) hC0 hAC hAn hAP
      (IsPGroup.of_card (n := 3) (by rw [hAcard]; norm_num)) hAc
  have hL1 : QCompOK 5 (⟨co2FiveLine 1, hmem 1⟩ : ↥co2P) := by
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
    exact qcompOK_of_derived_record (C := co2FiveC1) (D := co2FiveD) Nat.prime_five le_rfl
      (hmem 1) hC1 hD hDs hDnab hDP hDcent (hord 1) hcore (by rw [hDcard]; norm_num)
      (qtypeOK_A5 (Or.inr rfl)
        (@CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty _ _
          hDfin hDs hDcard).some)
  have hline : ∀ j, QCompOK 5 (⟨co2FiveLine j, hmem j⟩ : ↥co2P) := by
    intro j
    obtain ⟨hjP, hjconj⟩ := htrans j
    have hr : QCompOK 5 (⟨co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)), hmem _⟩ : ↥co2P) := by
      by_cases h : (j : ℕ) = 0
      · rw [(hrec0 j).2 h]; exact hL0
      · have h1 : co2FiveRecordOf j = 1 := by
          simp only [co2FiveRecordOf, h, if_false]
        rw [h1]; exact hL1
    have h := qcompOK_conj Nat.prime_five hnorm hjP (hmem _) hr
    have heq : (⟨co2FiveTransporter j * co2FiveLine (co2FiveRepLine (co2FiveRecordOf j)) *
        (co2FiveTransporter j)⁻¹, hnorm _ hjP _ (hmem _)⟩ : ↥co2P) =
        ⟨co2FiveLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @qrow_of_model .Co2 5 ↥co2P _ hfin hs hOut b hnc
    (@qcompOK_of_lines 2300 5 Nat.prime_five co2P co2FiveQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ co2FiveLine hlines hmem hline)

end Co2

section He7

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.RankThree.PartOne CFSG.Sporadic.HeldB


theorem qrow_He_seven (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    I1416QRow .He 7 := by
  have hp7 : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hp7⟩
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlinesSet, -⟩, htrans, hrecmem, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hC2, -⟩,
    ⟨hA0C, hA0n, hA0P, hA0card, -, -, hA0c⟩, ⟨hDs, hDnab, hDcard, hDP, hDcent, -⟩,
    ⟨hA2C, hA2n, hA2P, hA2card, -, hA2c⟩⟩ := R3E_He_full_seven_centralizer_structures
  have hM := heAutModel
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥heP := heEquivP
  have hfin : Finite ↥heP := inferInstance
  have hs : IsSimpleGroup ↥heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  have hc : Nat.card ↥heP = 4030387200 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.He.card_He
  have hpr : ¬ (Nat.card ↥heP).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥heP, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥heP _ hfin hs hpr
  have b : ↥heP ≃* (TauCeti.CFSGIndex.sporadic .He).Group := e.symm.trans (hbr .He).some
  have hlines := lines_of_eq hlinesSet
  have hlineQ : ∀ j, Subgroup.zpowers (heSevenLine j) ≤ heSevenQ ∧
      Nat.card (Subgroup.zpowers (heSevenLine j)) = 7 := by
    intro j
    have h : Subgroup.zpowers (heSevenLine j) ∈
        {H : Subgroup (Equiv.Perm (Fin 8330)) | H ≤ heSevenQ ∧ Nat.card H = 7} := by
      rw [hlinesSet]; exact ⟨j, rfl⟩
    exact h
  have hmem : ∀ j, heSevenLine j ∈ heP :=
    fun j => hQP ((hlineQ j).1 (Subgroup.mem_zpowers _))
  have hord : ∀ j, orderOf (heSevenLine j) = 7 := fun j => by
    rw [← Nat.card_zpowers]; exact (hlineQ j).2
  have hL0 : QCompOK 7 (⟨heSevenLine 0, hmem 0⟩ : ↥heP) :=
    qcompOK_of_pgroup_record hp7 hM.le (hmem 0) hC0 hA0C hA0n hA0P
      (IsPGroup.of_card (n := 3) (by rw [hA0card]; norm_num)) hA0c
  have hL2 : QCompOK 7 (⟨heSevenLine 2, hmem 2⟩ : ↥heP) :=
    qcompOK_of_pgroup_record hp7 hM.le (hmem 2) hC2 hA2C hA2n hA2P
      (IsPGroup.of_card (n := 2) (by rw [hA2card]; norm_num)) hA2c
  have hL1 : QCompOK 7 (⟨heSevenLine 1, hmem 1⟩ : ↥heP) := by
    have hDfin : Finite ↥heSevenD1 := Finite.of_injective (Subgroup.inclusion hDP)
      (Subgroup.inclusion_injective hDP)
    have hT : QTypeOK 7 ↥heSevenD1 := @qtypeOK_of_not_sq_dvd_aut 7 (by norm_num) _ _ hDfin
      (@not_sq_seven_dvd_card_mulAut_of_card_168 _ _ hDfin hDs hDcard)
    exact qcompOK_of_derived_record (C := heSevenC1) (D := heSevenD1) hp7 hM.le
      (hmem 1) hC1 rfl hDs hDnab hDP hDcent (hord 1)
      (gLAPPrimeCoreOf_inf_eq_bot_of_ambient hp7 hM.le hM.conj_mem
        (gLAPPrimeCoreOf_heSevenRecord_eq_bot 1 (Or.inr (Or.inl rfl))))
      (by rw [hDcard]; norm_num) hT
  have hline : ∀ j, QCompOK 7 (⟨heSevenLine j, hmem j⟩ : ↥heP) := by
    intro j
    obtain ⟨hjR, hjconj⟩ := htrans j
    have hr : QCompOK 7 (⟨heSevenLine (heSevenRecordOf j), hmem _⟩ : ↥heP) := by
      have h := hrecmem j
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · have : heSevenRecordOf j = 0 := Fin.ext h
        rw [this]; exact hL0
      · have : heSevenRecordOf j = 1 := Fin.ext h
        rw [this]; exact hL1
      · have : heSevenRecordOf j = 2 := Fin.ext h
        rw [this]; exact hL2
    have h := qcompOK_conj hp7 hM.conj_mem hjR (hmem _) hr
    have heq : (⟨heSevenTransporter j * heSevenLine (heSevenRecordOf j) *
        (heSevenTransporter j)⁻¹, hM.conj_mem _ hjR _ (hmem _)⟩ : ↥heP) =
        ⟨heSevenLine j, hmem j⟩ := Subtype.ext hjconj
    rw [heq] at h
    exact h
  exact @qrow_of_model .He 7 ↥heP _ hfin hs hOut b hnc
    (@qcompOK_of_lines 8330 7 hp7 heP heSevenQ hQP
      (card_eq_of_sylow_subgroupOf hQP hQsyl) _ heSevenLine hlines hmem hline)

end He7


end CFSG.LocalAnalysis.GLTheoremA.I1416QRows
