module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SevenSq
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAll
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Milestones.FAM_Th_simplicity
public import Certificates.Certificate10143
public import CFSG.LocalAnalysis.GLTheoremA.S8.HNAlt12
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

namespace ThPerf

section Certs


local notation "R7" => slpJ a b prog7

local notation "regs7" => slpRows (rowsOf seedA) (rowsOf seedB) 43 prog7

set_option maxRecDepth 100000

theorem perf_parts :
    eqRows (mulRows regs7[39]! regs7[31]!) idRows = true ∧
      eqRows (mulRows regs7[40]! regs7[34]!) idRows = true ∧
      rowsDiffer (wordRowsL regs7 sWords[0]!) idRows = true ∧
      ∀ i < 6, (sIdx[i]!).1 < 6 ∧ (sIdx[i]!).2 < 6 ∧
        perfAt regs7 (mulRows regs7[24]! (powRowsN regs7[25]! 6)) i = true := by
  have h := Certificates.certificate10143
  unfold thPerfOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun i hi => ⟨(h4 i hi).1.1, (h4 i hi).1.2, (h4 i hi).2⟩⟩

theorem rowsMatrix_reg {r : ℕ} (hr : r < 43) : rowsMatrix regs7[r]! = matJ (R7 r) :=
  rowsMatrix_regs7.2 r hr

theorem inv39 : R7 39 = (R7 31)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  exact eq_of_rowsMatrix_eq (by rw [rowsMatrix_mulRows, rowsMatrix_reg (by norm_num),
    rowsMatrix_reg (by norm_num), matJ_mul]) (by rw [rowsMatrix_idRows, matJ_one]) perf_parts.1

theorem inv40 : R7 40 = (R7 34)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  exact eq_of_rowsMatrix_eq (by rw [rowsMatrix_mulRows, rowsMatrix_reg (by norm_num),
    rowsMatrix_reg (by norm_num), matJ_mul]) (by rw [rowsMatrix_idRows, matJ_one])
    perf_parts.2.1

theorem invReg_spec {r : ℕ} (hr : okReg r = true) : R7 (invReg r) = (R7 r)⁻¹ := by
  unfold okReg at hr
  simp only [Bool.or_eq_true, beq_iff_eq] at hr
  rcases hr with ((rfl | rfl) | rfl) | rfl
  · rw [show invReg 31 = 39 by decide]; exact inv39
  · rw [show invReg 39 = 31 by decide, inv39, inv_inv]
  · rw [show invReg 34 = 40 by decide]; exact inv40
  · rw [show invReg 40 = 34 by decide, inv40, inv_inv]

theorem prod_invW {w : List ℕ} (hw : w.all okReg = true) :
    ((invW w).map R7).prod = ((w.map R7).prod)⁻¹ := by
  induction w with
  | nil => simp [invW]
  | cons r w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp only [invW, List.map_cons, List.reverse_cons, List.map_append, List.prod_append,
      List.map_reverse, List.map_map, List.prod_cons, mul_inv_rev] at ih ⊢
    rw [← List.map_reverse, ← List.map_map] at ih ⊢
    rw [ih hw.2]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Function.comp_apply]
    rw [invReg_spec hw.1]

theorem lt_of_okReg {w : List ℕ} (hw : w.all okReg = true) : ∀ r ∈ w, rowsMatrix regs7[r]! = matJ (R7 r) := by
  intro r hr
  have h := List.all_eq_true.1 hw r hr
  unfold okReg at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  apply rowsMatrix_reg
  rcases h with ((rfl | rfl) | rfl) | rfl <;> norm_num

theorem invW_okReg {w : List ℕ} (hw : w.all okReg = true) : (invW w).all okReg = true := by
  rw [List.all_eq_true] at hw ⊢
  intro r hr
  simp only [invW, List.mem_reverse, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  have h := hw r0 hr0
  unfold okReg at h ⊢
  simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with ((rfl | rfl) | rfl) | rfl <;> simp [invReg]

noncomputable def s (i : ℕ) : J := (sWords[i]!.map R7).prod

theorem s_facts (i : ℕ) (hi : i < 6) :
    s i * (R7 24 * R7 25 ^ 6) = (R7 24 * R7 25 ^ 6) * s i ∧
      ((sIdx[i]!).1 < 6 ∧ (sIdx[i]!).2 < 6) ∧
      s i = s (sIdx[i]!).1 * s (sIdx[i]!).2 * (s (sIdx[i]!).1)⁻¹ * (s (sIdx[i]!).2)⁻¹ := by
  obtain ⟨hj, hk, h⟩ := perf_parts.2.2.2 i hi
  unfold perfAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hw, hwj⟩, hwk⟩, hc⟩, he⟩ := h
  have hZ := rowsMatrix_z7
  refine ⟨?_, ⟨hj, hk⟩, ?_⟩
  · have e := eq_of_rowsMatrix_eq (g := s i * (R7 24 * R7 25 ^ 6))
      (h := (R7 24 * R7 25 ^ 6) * s i)
      (by rw [rowsMatrix_mulRows, rowsMatrix_wordRowsL (lt_of_okReg hw), hZ, matJ_mul]; rfl)
      (by rw [rowsMatrix_mulRows, rowsMatrix_wordRowsL (lt_of_okReg hw), hZ, matJ_mul]; rfl) hc
    exact e
  · have hall : ∀ r ∈ sWords[(sIdx[i]!).1]! ++ sWords[(sIdx[i]!).2]! ++
        invW sWords[(sIdx[i]!).1]! ++ invW sWords[(sIdx[i]!).2]!,
        rowsMatrix regs7[r]! = matJ (R7 r) := by
      intro r hr
      simp only [List.mem_append] at hr
      rcases hr with ((h1 | h1) | h1) | h1
      · exact lt_of_okReg hwj r h1
      · exact lt_of_okReg hwk r h1
      · exact lt_of_okReg (invW_okReg hwj) r h1
      · exact lt_of_okReg (invW_okReg hwk) r h1
    have e := eq_of_rowsMatrix_eq (rowsMatrix_wordRowsL (lt_of_okReg hw))
      (rowsMatrix_wordRowsL hall) he
    simp only [s]
    rw [e]
    simp only [List.map_append, List.prod_append, prod_invW hwj, prod_invW hwk]

theorem s0_ne_one : s 0 ≠ 1 := by
  obtain ⟨-, -, h⟩ := perf_parts.2.2.2 0 (by norm_num)
  unfold perfAt at h
  simp only [Bool.and_eq_true] at h
  exact ne_of_rowsDiffer (rowsMatrix_wordRowsL (lt_of_okReg h.1.1.1.1))
    (by rw [rowsMatrix_idRows, matJ_one]) perf_parts.2.2.1

theorem exists_component :
    ∃ J0 : Subgroup J, GLAPComponent 7 (Subgroup.centralizer ({R7 24 * R7 25 ^ 6} : Set J)) J0 := by
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  set L : Subgroup J := Subgroup.closure (s '' Set.Iio 6) with hL
  have hLC : L ≤ Subgroup.centralizer ({R7 24 * R7 25 ^ 6} : Set J) := by
    rw [hL, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (s_facts i hi).1
  have hperf : L ≤ ⁅L, L⁆ := by
    rw [hL, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨-, ⟨hj, hk⟩, he⟩ := s_facts i hi
    rw [SetLike.mem_coe, he, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨_, hj, rfl⟩)
      (Subgroup.subset_closure ⟨_, hk, rfl⟩)
  have hne : L ≠ ⊥ := by
    intro h
    apply s0_ne_one
    have : s 0 ∈ L := Subgroup.subset_closure ⟨0, by norm_num, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  exact exists_component_of_perfect_1176 orderOf_z7 card_centralizer_z7 hLC hperf hne

theorem kd264RowData_Th_seven : KD264RowData 7 J := by
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  obtain ⟨J0, hJ0⟩ := exists_component
  refine kd264RowData_of_sq (by norm_num) ?_ orderOf_z7 hJ0
  rw [CFSG.Sporadic.Th.Max3.natCard_J,
    show (90745943887872000 : ℕ) = 7 ^ 2 * 1851958038528000 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_seven.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

end Certs

end ThPerf


section Rows


set_option maxRecDepth 100000 in
theorem kd264SporAt_Th_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KD264SporAt 7 .Th := by
  haveI : Finite J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  haveI hTh : IsSimpleGroup NativeSporadic.Th := CFSG.Milestones.fam_th_simplicity
  haveI : IsSimpleGroup J := @MulEquiv.isSimpleGroup _ _ _ _ hTh thEquivJ.symm
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have hp : ¬ (Nat.card J).Prime := by
    rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num
  have hnc : ∃ x y : J, x * y ≠ y * x :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := J) hp
  have hb : J ≃* (TauCeti.CFSGIndex.sporadic .Th).Group := thEquivJ.symm.trans e
  have hrd : KD264RowData 7 J := ThPerf.kd264RowData_Th_seven
  refine kd264SporAt_of_model (p := 7) (s := .Th) (Q := J) hOut Nat.prime_seven (by decide) ?_ ?_
    ?_
  · exact hnc
  · exact hb
  · intro _ _ _
    exact hrd

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
