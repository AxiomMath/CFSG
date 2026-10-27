module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SevenSq
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAll
public import CFSG.LocalAnalysis.GLTheoremA.S8.HNAlt12
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo1
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Co1Seven
public import CFSG.Sporadic.Schreier.Co1SplitMono
public import CFSG.Sporadic.Bridge.Co1Surj
public import Certificates.Certificate10144
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.Native Timmesfeld.Co1Seven Timmesfeld.Co1SevenPerfect
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven

namespace Co1Perf

section Certs


set_option maxRecDepth 100000

theorem perf_parts :
    (gDag Native.aR Native.bR).2.2 = true ∧
      CFSG.Sporadic.Co1.InvNative.validRows
        (word (gDag Native.aR Native.bR).1 (gDag Native.aR Native.bR).2.1 sWords[0]!) = true ∧
      word (gDag Native.aR Native.bR).1 (gDag Native.aR Native.bR).2.1 sWords[0]! ≠ one () ∧
      ∀ i < 6, (sIdx[i]!).1 < 6 ∧ (sIdx[i]!).2 < 6 ∧
        perfAt (gDag Native.aR Native.bR).1 (gDag Native.aR Native.bR).2.1 i = true := by
  have h := Certificates.certificate10144
  unfold co1PerfOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun i hi => ⟨(h4 i hi).1.1, (h4 i hi).1.2, (h4 i hi).2⟩⟩

theorem listRep : ListRep (gDag Native.aR Native.bR).1 (gDag Native.aR Native.bR).2.1 gElts := by
  have hb : List.Forall₂ MRep [Native.aR, Native.bR] [A₁, A₂] :=
    List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil)
  exact dag_listRep hb (dagWords.map decWord) perf_parts.1

noncomputable def sw (w : List ℤ) : ↥GA := ⟨wordG gElts w, wordG_mem gElts_mem w⟩

theorem rep_sw (w : List ℤ) :
    MRep (word (gDag Native.aR Native.bR).1 (gDag Native.aR Native.bR).2.1 w)
      ((sw w : ↥GA) : GL24) :=
  MRep.word listRep w

theorem wordG_append (gs : List GL24) (u v : List ℤ) :
    wordG gs (u ++ v) = wordG gs u * wordG gs v := by
  unfold wordG
  rw [List.foldl_append]
  generalize wordG gs u = x
  suffices ∀ y : GL24, v.foldl (fun x j => x * letterG gs j) y =
      y * v.foldl (fun x j => x * letterG gs j) 1 by rw [this]
  induction v with
  | nil => intro y; simp
  | cons j v ih =>
    intro y
    rw [List.foldl_cons, List.foldl_cons, ih, ih (1 * letterG gs j), one_mul, mul_assoc]

theorem letterG_neg (gs : List GL24) {j : ℤ} (hj : j ≠ 0) :
    letterG gs (-j) = (letterG gs j)⁻¹ := by
  unfold letterG
  rcases lt_or_gt_of_ne hj with h | h
  · rw [if_pos (by omega), if_neg (by omega), inv_inv]
  · rw [if_neg (by omega), if_pos h, neg_neg]

theorem wordG_single (gs : List GL24) (j : ℤ) : wordG gs [j] = letterG gs j := by
  simp [wordG]

theorem wordG_invW (gs : List GL24) {w : List ℤ} (hw : w.all okLetter = true) :
    wordG gs (invW w) = (wordG gs w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordG]
  | cons j w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    have hj : j ≠ 0 := by
      have := hw.1
      unfold okLetter at this
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      omega
    have e : invW (j :: w) = invW w ++ [-j] := by simp [invW]
    rw [e, wordG_append, ih hw.2, show (j :: w) = [j] ++ w from rfl, wordG_append, mul_inv_rev,
      wordG_single, wordG_single, letterG_neg gs hj]

noncomputable def s (i : ℕ) : ↥GA := sw sWords[i]!

theorem s_facts (i : ℕ) (hi : i < 6) :
    s i * tE = tE * s i ∧ ((sIdx[i]!).1 < 6 ∧ (sIdx[i]!).2 < 6) ∧
      s i = s (sIdx[i]!).1 * s (sIdx[i]!).2 * (s (sIdx[i]!).1)⁻¹ * (s (sIdx[i]!).2)⁻¹ := by
  obtain ⟨hj, hk, h⟩ := perf_parts.2.2.2 i hi
  unfold perfAt at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hw, hc0⟩, he0⟩ := h
  have hc := beq_iff_eq.1 hc0
  have he := beq_iff_eq.1 he0
  have hT : MRep (rowAt (gDag Native.aR Native.bR).1 iT) ((tE : ↥GA) : GL24) :=
    rep_gE perf_parts.1 iT
  refine ⟨?_, ⟨hj, hk⟩, ?_⟩
  · apply Subtype.ext
    have h1 := (rep_sw sWords[i]!).mul hT
    have h2 := hT.mul (rep_sw sWords[i]!)
    rw [hc] at h1
    exact MRep.eq h1 h2
  · apply Subtype.ext
    have h1 := rep_sw sWords[i]!
    rw [he] at h1
    have h2 := MRep.eq h1 (rep_sw _)
    show ((sw sWords[i]! : ↥GA) : GL24) = _
    rw [h2]
    have hwj : sWords[(sIdx[i]!).1]!.all okLetter = true := by
      have := (perf_parts.2.2.2 _ hj).2.2
      unfold perfAt at this
      simp only [Bool.and_eq_true] at this
      exact this.1.1
    have hwk : sWords[(sIdx[i]!).2]!.all okLetter = true := by
      have := (perf_parts.2.2.2 _ hk).2.2
      unfold perfAt at this
      simp only [Bool.and_eq_true] at this
      exact this.1.1
    simp only [sw, s, wordG_append, wordG_invW gElts hwj, wordG_invW gElts hwk, Subgroup.coe_mul,
      Subgroup.coe_inv]

theorem s0_ne_one : s 0 ≠ 1 := by
  intro h
  have hr := rep_sw sWords[0]!
  rw [show sw sWords[0]! = s 0 from rfl, h, Subgroup.coe_one] at hr
  exact perf_parts.2.2.1 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.rows_eq_of_mrep
    perf_parts.2.1 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.validRows_one hr MRep.one)

end Certs

section Comp


theorem exists_component :
    ∃ J0 : Subgroup ↥GA, GLAPComponent 7 (Subgroup.centralizer ({tE} : Set ↥GA)) J0 := by
  haveI : Finite ↥GA := finite_GA
  have hS : sylowOK Native.aR Native.bR = true := Certificates.certificate13696
  set L : Subgroup ↥GA := Subgroup.closure (s '' Set.Iio 6) with hL
  have hLC : L ≤ Subgroup.centralizer ({tE} : Set ↥GA) := by
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
  exact exists_component_of_perfect_1176 (orderOf_tE hS)
    CFSG.HardMathSupport.Solomon.Coordinator.Co1Spor.card_centralizer_tE hLC hperf hne

theorem kd264RowData_Co1_seven : KD264RowData 7 ↥GA := by
  haveI : Finite ↥GA := finite_GA
  have hS : sylowOK Native.aR Native.bR = true := Certificates.certificate13696
  obtain ⟨J0, hJ0⟩ := exists_component
  exact kd264RowData_of_sq (by norm_num) factorization_card_GA_seven (orderOf_tE hS) hJ0

end Comp

end Co1Perf

section Rows


set_option maxRecDepth 100000 in
theorem kd264SporAt_Co1_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KD264SporAt 7 .Co1 := by
  haveI : Finite ↥GA := finite_GA
  haveI : IsSimpleGroup ↥GA := CFSG.HardMathSupport.Dickson.I271.co1_isSimple
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have hp : ¬ (Nat.card ↥GA).Prime := by
    intro h
    have h7 := factorization_card_GA_seven
    rw [h.factorization] at h7
    by_cases h72 : Nat.card ↥GA = 7
    · rw [h72, Finsupp.single_eq_same] at h7; omega
    · rw [Finsupp.single_eq_of_ne (Ne.symm h72)] at h7; omega
  have hnc : ∃ x y : ↥GA, x * y ≠ y * x :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥GA) hp
  have hb : ↥GA ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group :=
    CFSG.Sporadic.Co1Block.co1MatEquiv.symm.trans e
  have hrd : KD264RowData 7 ↥GA := Co1Perf.kd264RowData_Co1_seven
  refine kd264SporAt_of_model (p := 7) (s := .Co1) (Q := ↥GA) hOut Nat.prime_seven (by decide) ?_
    ?_ ?_
  · exact hnc
  · exact hb
  · intro _ _ _
    exact hrd

end Rows

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
