module

public import CFSG.ClassicalInvolution.Phan.PhanDn.KleinDickson
public import CFSG.ClassicalInvolution.Phan.PhanDn.Chambers
public import CFSG.ClassicalInvolution.Phan.SimplyConnected
public import CFSG.ClassicalInvolution.Phan.PanelLift
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan
open CFSG.RankThree.PartOne.K159
open CFSG.Monster.B.Geometry Module Matrix
open scoped Pointwise

variable {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}

@[expose] def kleinLine (A B : Submodule K (Fin 4 → K)) : Submodule K (Fin 3 ⊕ Fin 3 → K) :=
  Submodule.span K (Set.image2 kleinWedge A B)

omit [CharP K 2] in
theorem kleinLine_span_singleton (u v : Fin 4 → K) :
    kleinLine (K ∙ u) (K ∙ v) = K ∙ kleinWedge u v := by
  rw [kleinLine]
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [kleinWedge_smul_left, kleinWedge_smul_right, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    exact Submodule.subset_span
      ⟨u, Submodule.mem_span_singleton_self u, v, Submodule.mem_span_singleton_self v, rfl⟩

private noncomputable def kleinGen (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    Fin 4 → Fin 4 → K :=
  (c.exists_gen hσ).choose

omit [CharP K 2] in
private theorem kleinGen_line (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) (k : Fin 4) :
    c.line k = K ∙ kleinGen hσ c k :=
  (c.exists_gen hσ).choose_spec.1 k

omit [CharP K 2] in
private theorem kleinGen_herm (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) (j k : Fin 4) :
    herm σ (kleinGen hσ c j) (kleinGen hσ c k) = if j = k then 1 else 0 :=
  (c.exists_gen hσ).choose_spec.2 j k

private noncomputable def kleinFrame (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    FlipFrame σ 3 where
  line j := K ∙ kleinWedge (kleinGen hσ c 0) (kleinGen hσ c j.succ)
  isFlipflopPt_line j := by
    have h00 : herm σ (kleinGen hσ c 0) (kleinGen hσ c 0) = 1 := by
      rw [kleinGen_herm]; exact if_pos rfl
    have hjj : herm σ (kleinGen hσ c j.succ) (kleinGen hσ c j.succ) = 1 := by
      rw [kleinGen_herm]; exact if_pos rfl
    have hj0 : herm σ (kleinGen hσ c j.succ) (kleinGen hσ c 0) = 0 := by
      rw [kleinGen_herm]; exact if_neg (Fin.succ_ne_zero j)
    have h0j : herm σ (kleinGen hσ c 0) (kleinGen hσ c j.succ) = 0 := by
      rw [kleinGen_herm]; exact if_neg fun h => Fin.succ_ne_zero j h.symm
    have hone : flipHerm σ (kleinWedge (kleinGen hσ c 0) (kleinGen hσ c j.succ))
        (kleinWedge (kleinGen hσ c 0) (kleinGen hσ c j.succ)) = 1 := by
      rw [flipHerm_kleinWedge, h00, hjj, hj0, h0j, mul_one, mul_zero, add_zero]
    have hw : kleinWedge (kleinGen hσ c 0) (kleinGen hσ c j.succ) ≠ 0 := by
      intro h0
      rw [h0, flipHerm_zero_left] at hone
      exact zero_ne_one hone
    exact (isFlipflopPt_span_singleton_iff hw).mpr
      ⟨quadPlus_kleinWedge _ _, by rw [hone]; exact one_ne_zero⟩
  polar_eq_zero j k hjk u hu v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      polar_kleinWedge_left, smul_zero, smul_zero]
  flipHerm_eq_zero j k hjk u hu v hv := by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv
    have h00 : herm σ (kleinGen hσ c 0) (kleinGen hσ c 0) = 1 := by
      rw [kleinGen_herm]; exact if_pos rfl
    have hkj : herm σ (kleinGen hσ c k.succ) (kleinGen hσ c j.succ) = 0 := by
      rw [kleinGen_herm]
      exact if_neg fun h => hjk (by
        have h' := congrArg Fin.val h
        simp only [Fin.val_succ] at h'
        exact Fin.ext (by omega))
    have hk0 : herm σ (kleinGen hσ c k.succ) (kleinGen hσ c 0) = 0 := by
      rw [kleinGen_herm]; exact if_neg (Fin.succ_ne_zero k)
    have h0j : herm σ (kleinGen hσ c 0) (kleinGen hσ c j.succ) = 0 := by
      rw [kleinGen_herm]; exact if_neg fun h => Fin.succ_ne_zero j h.symm
    rw [flipHerm_smul_left, flipHerm_smul_right, flipHerm_kleinWedge, h00, hkj, hk0, h0j]
    ring

private theorem kleinFrame_line (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) (j : Fin 3) :
    (kleinFrame hσ c).line j =
      K ∙ kleinWedge (kleinGen hσ c 0) (kleinGen hσ c j.succ) :=
  rfl

private theorem kleinFrame_line_eq_kleinLine (hσ : IsUnitaryInvolution σ) (c : Frame σ 4)
    (j : Fin 3) : (kleinFrame hσ c).line j = kleinLine (c.line 0) (c.line j.succ) := by
  rw [kleinFrame_line, kleinGen_line, kleinGen_line, kleinLine_span_singleton]

private theorem kleinFrame_stdFrame (hσ : IsUnitaryInvolution σ) (j : Fin 3) :
    (kleinFrame hσ (stdFrame σ 4)).line j = K ∙ stdE (K := K) (n := 3) j := by
  rw [kleinFrame_line_eq_kleinLine, stdFrame_line, stdFrame_line,
    kleinLine_span_singleton, kleinWedge_single_zero]

private theorem kleinFrame_line_smul (hσ : IsUnitaryInvolution σ) (g : SUid σ 4)
    (c : Frame σ 4) (j : Fin 3) :
    (kleinFrame hσ (g • c)).line j =
      ((kleinFrame hσ c).line j).map
        (Klein.cong ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  rw [kleinFrame_line_eq_kleinLine, kleinFrame_line_eq_kleinLine, Frame.smul_line,
    Frame.smul_line, kleinGen_line hσ c 0, kleinGen_line hσ c j.succ,
    smul_span_singleton, smul_span_singleton, kleinLine_span_singleton,
    kleinLine_span_singleton, Submodule.map_span, Set.image_singleton]
  simp only [smul_def, kleinWedge_mulVec]

omit [CharP K 2] in
private theorem kleinWedge_zero_right (u : Fin 4 → K) : kleinWedge u 0 = 0 := by
  simpa using kleinWedge_smul_right (0 : K) u (0 : Fin 4 → K)

omit [CharP K 2] in
private theorem kleinLine_sup_left (A B C : Submodule K (Fin 4 → K)) :
    kleinLine (A ⊔ B) C = kleinLine A C ⊔ kleinLine B C := by
  refine le_antisymm ?_ ?_
  · rw [kleinLine]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [kleinWedge_add_left]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, y, hy, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, y, hy, rfl⟩))
  · refine sup_le ?_ ?_
    · rw [kleinLine]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Submodule.subset_span ⟨x, Submodule.mem_sup_left hx, y, hy, rfl⟩
    · rw [kleinLine]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Submodule.subset_span ⟨x, Submodule.mem_sup_right hx, y, hy, rfl⟩

omit [CharP K 2] in
private theorem kleinLine_sup_right (A B C : Submodule K (Fin 4 → K)) :
    kleinLine A (B ⊔ C) = kleinLine A B ⊔ kleinLine A C := by
  refine le_antisymm ?_ ?_
  · rw [kleinLine]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [kleinWedge_add_right]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, a, ha, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, b, hb, rfl⟩))
  · refine sup_le ?_ ?_
    · rw [kleinLine]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Submodule.subset_span ⟨x, hx, y, Submodule.mem_sup_left hy, rfl⟩
    · rw [kleinLine]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Submodule.subset_span ⟨x, hx, y, Submodule.mem_sup_right hy, rfl⟩

omit [CharP K 2] in
private theorem kleinLine_bot_right (A : Submodule K (Fin 4 → K)) :
    kleinLine A (⊥ : Submodule K (Fin 4 → K)) = ⊥ := by
  rw [kleinLine]
  simp [kleinWedge_zero_right]

omit [CharP K 2] in
private theorem kleinLine_finset_sup_right (S : Finset (Fin 4))
    (f : Fin 4 → Submodule K (Fin 4 → K)) (A : Submodule K (Fin 4 → K)) :
    kleinLine A (S.sup f) = S.sup fun i => kleinLine A (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.sup_empty, kleinLine_bot_right]
  | insert i S hi ih => rw [Finset.sup_insert, Finset.sup_insert, kleinLine_sup_right, ih]

omit [CharP K 2] in
private theorem dFlip_zero : dFlip σ (0 : Fin 3 ⊕ Fin 3 → K) = 0 := by
  simpa using dFlip_smul (0 : K) (0 : Fin 3 ⊕ Fin 3 → K)

private theorem dFlip_kleinWedge_orthonormal_apply {b : Fin 4 → Fin 4 → K}
    (hb : ∀ j k, herm σ (b j) (b k) = if j = k then 1 else 0) {i j k l : Fin 4}
    (hstd : dFlip σ (kleinWedge (Pi.single i 1 : Fin 4 → K) (Pi.single j 1 : Fin 4 → K)) =
      kleinWedge (Pi.single k 1 : Fin 4 → K) (Pi.single l 1 : Fin 4 → K)) :
    dFlip σ (kleinWedge (b i) (b j)) = σ (colMat b).det • kleinWedge (b k) (b l) := by
  have hcol : ∀ i : Fin 4, (colMat b) *ᵥ (Pi.single i 1 : Fin 4 → K) = b i := by
    intro i
    rw [Matrix.mulVec_single_one]
    rfl
  have hunit : conjTr σ (colMat b) * colMat b = 1 := conjTr_colMat_mul_colMat hb
  have hcong : kleinWedge (b i) (b j) =
      Klein.cong (colMat b) (kleinWedge (Pi.single i 1 : Fin 4 → K) (Pi.single j 1)) := by
    rw [← kleinWedge_mulVec, hcol, hcol]
  rw [hcong, dFlip_cong_of_unitary hunit, hstd, ← kleinWedge_mulVec, hcol, hcol]

private theorem kleinFrame_star (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    kleinLine (c.line 0) (⊤ : Submodule K (Fin 4 → K)) =
      (kleinFrame hσ c).line 0 ⊔ (kleinFrame hσ c).line 1 ⊔ (kleinFrame hσ c).line 2 := by
  have htop : (⊤ : Submodule K (Fin 4 → K)) = Finset.univ.sup c.line := by
    rw [← c.spanAt_univ hσ]
    rfl
  rw [htop, kleinLine_finset_sup_right]
  simp only [kleinGen_line hσ c, kleinFrame_line, kleinLine_span_singleton]
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp only [Finset.sup_insert, Finset.sup_singleton, kleinWedge_self,
    Submodule.span_zero_singleton]
  simp [sup_assoc]

omit [CharP K 2] in
private theorem spanAt_zero_one_two (c : Frame σ 4) :
    c.spanAt ({0, 1, 2} : Finset (Fin 4)) = c.line 0 ⊔ c.line 1 ⊔ c.line 2 := by
  rw [show ({0, 1, 2} : Finset (Fin 4)) = insert 2 {0, 1} by decide]
  rw [Frame.spanAt_insert, Frame.spanAt_pair]
  ac_rfl

omit [CharP K 2] in
private theorem spanAt_one_two_three (c : Frame σ 4) :
    c.spanAt ({1, 2, 3} : Finset (Fin 4)) = c.line 1 ⊔ c.line 2 ⊔ c.line 3 := by
  rw [show ({1, 2, 3} : Finset (Fin 4)) = insert 3 {1, 2} by decide]
  rw [Frame.spanAt_insert, Frame.spanAt_pair]
  ac_rfl

private theorem kleinLine_spanAt_pair (hσ : IsUnitaryInvolution σ) (c : Frame σ 4)
    (i j : Fin 4) (_hij : i ≠ j) :
    kleinLine (c.spanAt {i, j}) (c.spanAt {i, j}) =
      K ∙ kleinWedge (kleinGen hσ c i) (kleinGen hσ c j) := by
  rw [Frame.spanAt_pair, kleinGen_line hσ c i, kleinGen_line hσ c j]
  simp only [kleinLine_sup_left, kleinLine_sup_right, kleinLine_span_singleton,
    kleinWedge_self, Submodule.span_zero_singleton, sup_bot_eq]
  rw [show kleinWedge (kleinGen hσ c j) (kleinGen hσ c i) =
    kleinWedge (kleinGen hσ c i) (kleinGen hσ c j) from
      kleinWedge_comm (kleinGen hσ c j) (kleinGen hσ c i)]
  simp

private theorem kleinLine_spanAt_zero_one_two (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    kleinLine (c.spanAt ({0, 1, 2} : Finset (Fin 4)))
        (c.spanAt ({0, 1, 2} : Finset (Fin 4))) =
      K ∙ kleinWedge (kleinGen hσ c 0) (kleinGen hσ c 1) ⊔
      K ∙ kleinWedge (kleinGen hσ c 0) (kleinGen hσ c 2) ⊔
      K ∙ kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 2) := by
  rw [spanAt_zero_one_two, kleinGen_line hσ c 0, kleinGen_line hσ c 1,
    kleinGen_line hσ c 2]
  simp only [kleinLine_sup_left, kleinLine_sup_right, kleinLine_span_singleton,
    kleinWedge_self, Submodule.span_zero_singleton, sup_bot_eq]
  rw [show kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 0) =
      kleinWedge (kleinGen hσ c 0) (kleinGen hσ c 1) from
        kleinWedge_comm (kleinGen hσ c 1) (kleinGen hσ c 0),
    show kleinWedge (kleinGen hσ c 2) (kleinGen hσ c 0) =
      kleinWedge (kleinGen hσ c 0) (kleinGen hσ c 2) from
        kleinWedge_comm (kleinGen hσ c 2) (kleinGen hσ c 0),
    show kleinWedge (kleinGen hσ c 2) (kleinGen hσ c 1) =
      kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 2) from
        kleinWedge_comm (kleinGen hσ c 2) (kleinGen hσ c 1)]
  rw [bot_sup_eq]
  ac_rfl

private theorem kleinLine_spanAt_one_two_three (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    kleinLine (c.spanAt ({1, 2, 3} : Finset (Fin 4)))
        (c.spanAt ({1, 2, 3} : Finset (Fin 4))) =
      K ∙ kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 2) ⊔
      K ∙ kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 3) ⊔
      K ∙ kleinWedge (kleinGen hσ c 2) (kleinGen hσ c 3) := by
  rw [spanAt_one_two_three, kleinGen_line hσ c 1, kleinGen_line hσ c 2,
    kleinGen_line hσ c 3]
  simp only [kleinLine_sup_left, kleinLine_sup_right, kleinLine_span_singleton,
    kleinWedge_self, Submodule.span_zero_singleton, sup_bot_eq]
  rw [show kleinWedge (kleinGen hσ c 2) (kleinGen hσ c 1) =
      kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 2) from
        kleinWedge_comm (kleinGen hσ c 2) (kleinGen hσ c 1),
    show kleinWedge (kleinGen hσ c 3) (kleinGen hσ c 1) =
      kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 3) from
        kleinWedge_comm (kleinGen hσ c 3) (kleinGen hσ c 1),
    show kleinWedge (kleinGen hσ c 3) (kleinGen hσ c 2) =
      kleinWedge (kleinGen hσ c 2) (kleinGen hσ c 3) from
        kleinWedge_comm (kleinGen hσ c 3) (kleinGen hσ c 2)]
  rw [bot_sup_eq]
  ac_rfl

private theorem kleinFrame_even_ruling (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    Even (3 - Module.finrank K ↥((kleinFrame hσ c).spanAt Finset.univ ⊓ stdLag 3 K)) := by
  classical
  obtain ⟨g, hg⟩ := exists_smul_stdFrame (σ := σ) hσ c
  let G : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hdet : G.det = 1 := (mem_SUid.mp g.2).1
  have hgen : ∀ k : Fin 4, c.line k = K ∙ (g • (Pi.single k 1 : Fin 4 → K)) := by
    intro k
    rw [← hg, Frame.smul_line, stdFrame_line, smul_span_singleton]
  have hcoef : ∀ k : Fin 4, ∃ a : K, a ≠ 0 ∧
      kleinGen hσ c k = a • (g • (Pi.single k 1 : Fin 4 → K)) := by
    intro k
    have hspan : K ∙ kleinGen hσ c k = K ∙ (g • (Pi.single k 1 : Fin 4 → K)) := by
      rw [← kleinGen_line hσ c k, hgen k]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (hspan ▸ Submodule.mem_span_singleton_self (kleinGen hσ c k))
    have hv0 : kleinGen hσ c k ≠ 0 := by
      intro h0
      have h1 : Module.finrank K (K ∙ kleinGen hσ c k) = 1 := by
        rw [← kleinGen_line hσ c k]; exact c.finrank_line k
      rw [h0, Submodule.span_zero_singleton, finrank_bot] at h1
      exact zero_ne_one h1
    refine ⟨a, ?_, ha.symm⟩
    rintro rfl
    rw [zero_smul] at ha
    exact hv0 ha.symm
  have hline : ∀ j : Fin 3, (kleinFrame hσ c).line j =
      K ∙ (Klein.cong G (stdE (K := K) (n := 3) j)) := by
    intro j
    obtain ⟨a, ha, hv⟩ := hcoef 0
    obtain ⟨b, hb, hw⟩ := hcoef j.succ
    have hwedge : kleinWedge (g • (Pi.single 0 1 : Fin 4 → K))
        (g • (Pi.single j.succ 1 : Fin 4 → K)) =
        Klein.cong G (stdE (K := K) (n := 3) j) := by
      simp only [smul_def]
      rw [kleinWedge_mulVec, kleinWedge_single_zero]
    rw [kleinFrame_line]
    calc K ∙ kleinWedge (kleinGen hσ c 0) (kleinGen hσ c j.succ)
        = K ∙ ((a * b) • kleinWedge (g • (Pi.single 0 1 : Fin 4 → K))
            (g • (Pi.single j.succ 1 : Fin 4 → K))) := by
          rw [hv, hw, kleinWedge_smul_left, kleinWedge_smul_right, smul_smul]
      _ = K ∙ kleinWedge (g • (Pi.single 0 1 : Fin 4 → K))
            (g • (Pi.single j.succ 1 : Fin 4 → K)) :=
          Submodule.span_singleton_smul_eq (IsUnit.mk0 (a * b) (mul_ne_zero ha hb)) _
      _ = K ∙ (Klein.cong G (stdE (K := K) (n := 3) j)) := by rw [hwedge]
  have hspan : (kleinFrame hσ c).spanAt Finset.univ = (stdLag 3 K).map (Klein.cong G) := by
    rw [FlipFrame.spanAt, Finset.sup_univ_eq_iSup]
    have hsup : (⨆ j : Fin 3, (kleinFrame hσ c).line j) =
        ⨆ j : Fin 3, K ∙ (Klein.cong G (stdE (K := K) (n := 3) j)) :=
      iSup_congr fun j => hline j
    rw [hsup, ← Submodule.span_range_eq_iSup, stdLag_eq_span_stdE, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨stdE (K := K) (n := 3) j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  let g' : SpecialLinearGroup (Fin 4) K := ⟨G, hdet⟩
  have hD : kleinDickson (K := K) ⟨Klein.rho g', Klein.rho_mem g'⟩ = 1 := kleinDickson_rho g'
  have hEven := (kleinDickson_eq_one_iff (K := K) ⟨Klein.rho g', Klein.rho_mem g'⟩).mp hD
  rw [hspan]
  exact hEven

noncomputable def kleinChamber (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) : DChamber σ 3 where
  toFlipFrame := kleinFrame hσ c
  even_ruling := kleinFrame_even_ruling hσ c

theorem kleinChamber_line_smul (hσ : IsUnitaryInvolution σ) (g : SUid σ 4) (c : Frame σ 4)
    (j : Fin 3) : (kleinChamber hσ (g • c)).line j =
      ((kleinChamber hσ c).line j).map
        (Klein.cong ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :=
  kleinFrame_line_smul hσ g c j

theorem kleinChamber_stdFrame (hσ : IsUnitaryInvolution σ) (j : Fin 3) :
    (kleinChamber hσ (stdFrame σ 4)).line j = K ∙ stdE (K := K) (n := 3) j :=
  kleinFrame_stdFrame hσ j

omit [CharP K 2] in
private theorem flipSpanAt_singleton (c : FlipFrame σ 3) (a : Fin 3) :
    c.spanAt ({a} : Finset (Fin 3)) = c.line a := by
  rw [show ({a} : Finset (Fin 3)) = insert a ∅ by simp, FlipFrame.spanAt_insert,
    FlipFrame.spanAt_empty, sup_bot_eq]

omit [CharP K 2] in
private theorem flipSpanAt_pair (c : FlipFrame σ 3) (a b : Fin 3) :
    c.spanAt ({a, b} : Finset (Fin 3)) = c.line a ⊔ c.line b := by
  rw [show ({a, b} : Finset (Fin 3)) = insert a {b} by simp, FlipFrame.spanAt_insert,
    flipSpanAt_singleton]

private theorem dFlipSub_kleinFrame_line_of_std (hσ : IsUnitaryInvolution σ) (c : Frame σ 4)
    (j : Fin 3) {k l : Fin 4}
    (hstd : dFlip σ (stdE (K := K) (n := 3) j) =
      kleinWedge (Pi.single k 1 : Fin 4 → K) (Pi.single l 1 : Fin 4 → K)) :
    dFlipSub σ ((kleinFrame hσ c).line j) =
      K ∙ kleinWedge (kleinGen hσ c k) (kleinGen hσ c l) := by
  have hunit : conjTr σ (colMat (kleinGen hσ c)) * colMat (kleinGen hσ c) = 1 :=
    conjTr_colMat_mul_colMat (kleinGen_herm hσ c)
  have hdet : (colMat (kleinGen hσ c)).det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hunit
  rw [← kleinWedge_single_zero (K := K) (j := j)] at hstd
  have hd := dFlip_kleinWedge_orthonormal_apply (kleinGen_herm hσ c) (i := 0) (j := j.succ) hstd
  rw [kleinFrame_line, dFlipSub_span_singleton, hd]
  exact Submodule.span_singleton_smul_eq
    (IsUnit.mk0 (σ (colMat (kleinGen hσ c)).det) ((map_ne_zero σ).mpr hdet)) _

private theorem kleinFrame_dFlip_line_zero (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    dFlipSub σ ((kleinFrame hσ c).line 0) =
      K ∙ kleinWedge (kleinGen hσ c 2) (kleinGen hσ c 3) := by
  refine dFlipSub_kleinFrame_line_of_std hσ c 0 (k := 2) (l := 3) ?_
  rw [dFlip_stdE, stdF_eq_kleinWedge.1]

private theorem kleinFrame_dFlip_line_one (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    dFlipSub σ ((kleinFrame hσ c).line 1) =
      K ∙ kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 3) := by
  refine dFlipSub_kleinFrame_line_of_std hσ c 1 (k := 1) (l := 3) ?_
  rw [dFlip_stdE, stdF_eq_kleinWedge.2.1]

private theorem kleinFrame_dFlip_line_two (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    dFlipSub σ ((kleinFrame hσ c).line 2) =
      K ∙ kleinWedge (kleinGen hσ c 1) (kleinGen hσ c 2) := by
  refine dFlipSub_kleinFrame_line_of_std hσ c 2 (k := 1) (l := 2) ?_
  rw [dFlip_stdE, stdF_eq_kleinWedge.2.2]

theorem dFlipSub_kleinLine_line_zero (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    dFlipSub σ (kleinLine (c.line 0) ⊤) =
      kleinLine (c.spanAt ({1, 2, 3} : Finset (Fin 4)))
        (c.spanAt ({1, 2, 3} : Finset (Fin 4))) := by
  rw [kleinFrame_star (hσ := hσ) (c := c), kleinLine_spanAt_one_two_three hσ c,
    dFlipSub_sup hσ.invol, dFlipSub_sup hσ.invol, kleinFrame_dFlip_line_zero,
    kleinFrame_dFlip_line_one, kleinFrame_dFlip_line_two]
  ac_rfl

theorem elt_kleinChamber_zero (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    (kleinChamber hσ c).elt 0 = kleinLine (c.spanAt ({0, 1} : Finset (Fin 4)))
      (c.spanAt ({0, 1} : Finset (Fin 4))) := by
  have hlast : (0 : Fin 3) ≠ Fin.last 2 := by decide
  have hmid : ¬ ((0 : Fin 3) : ℕ) + 1 = 2 := by decide
  rw [FlipFrame.elt, if_neg hlast, if_neg hmid]
  have hsub : (kleinFrame hσ c).sub 1 = (kleinFrame hσ c).line 0 := by
    rw [FlipFrame.sub,
      show (Finset.univ.filter fun l : Fin 3 => (l : ℕ) < 1) = {0} by decide]
    exact flipSpanAt_singleton _ 0
  change (kleinFrame hσ c).sub 1 = kleinLine (c.spanAt ({0, 1} : Finset (Fin 4)))
    (c.spanAt ({0, 1} : Finset (Fin 4)))
  rw [hsub, kleinFrame_line, kleinLine_spanAt_pair hσ c 0 1 (by decide)]
  rw [show (Fin.succ (0 : Fin 3)) = (1 : Fin 4) by decide]

theorem elt_kleinChamber_one (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    (kleinChamber hσ c).elt 1 = kleinLine (c.spanAt ({0, 1, 2} : Finset (Fin 4)))
      (c.spanAt ({0, 1, 2} : Finset (Fin 4))) := by
  have hlast : (1 : Fin 3) ≠ Fin.last 2 := by decide
  have hmid : ((1 : Fin 3) : ℕ) + 1 = 2 := by decide
  rw [FlipFrame.elt, if_neg hlast, if_pos hmid, FlipFrame.alt]
  have hsub : (kleinFrame hσ c).sub 2 =
      (kleinFrame hσ c).line 0 ⊔ (kleinFrame hσ c).line 1 := by
    rw [FlipFrame.sub,
      show (Finset.univ.filter fun l : Fin 3 => (l : ℕ) < 2) = {0, 1} by decide]
    exact flipSpanAt_pair _ 0 1
  change (kleinFrame hσ c).sub 2 ⊔ dFlipSub σ ((kleinFrame hσ c).line 2) =
    kleinLine (c.spanAt ({0, 1, 2} : Finset (Fin 4)))
      (c.spanAt ({0, 1, 2} : Finset (Fin 4)))
  rw [hsub, kleinFrame_dFlip_line_two, kleinFrame_line, kleinFrame_line,
    kleinLine_spanAt_zero_one_two hσ c]
  ac_rfl

theorem elt_kleinChamber_two (hσ : IsUnitaryInvolution σ) (c : Frame σ 4) :
    (kleinChamber hσ c).elt 2 = kleinLine (c.line 0) ⊤ := by
  have hlast : (2 : Fin 3) = Fin.last 2 := by decide
  rw [FlipFrame.elt, if_pos hlast]
  have hsub : (kleinFrame hσ c).sub 3 =
      (kleinFrame hσ c).line 0 ⊔ (kleinFrame hσ c).line 1 ⊔ (kleinFrame hσ c).line 2 := by
    rw [FlipFrame.sub,
      show (Finset.univ.filter fun l : Fin 3 => (l : ℕ) < 3) = {0, 1, 2} by decide,
      show ({0, 1, 2} : Finset (Fin 3)) = insert 2 {0, 1} by decide,
      FlipFrame.spanAt_insert, flipSpanAt_pair]
    ac_rfl
  change (kleinFrame hσ c).sub 3 = kleinLine (c.line 0) ⊤
  rw [hsub, ← kleinFrame_star hσ c]

private theorem contract_eq_mulVec (φ : Fin 4 → K) (X : Fin 3 ⊕ Fin 3 → K) :
    contract φ X = Klein.alt X *ᵥ φ := by
  rw [contract, ← Matrix.mulVec_transpose, Klein.alt_transpose]

private theorem contract_add (φ : Fin 4 → K) (X Y : Fin 3 ⊕ Fin 3 → K) :
    contract φ (X + Y) = contract φ X + contract φ Y := by
  simp only [contract_eq_mulVec, Klein.alt_add, Matrix.add_mulVec]

private theorem contract_smul (φ : Fin 4 → K) (a : K) (X : Fin 3 ⊕ Fin 3 → K) :
    contract φ (a • X) = a • contract φ X := by
  simp only [contract_eq_mulVec, Klein.alt_smul, Matrix.smul_mulVec]

private theorem contract_zero (φ : Fin 4 → K) :
    contract φ (0 : Fin 3 ⊕ Fin 3 → K) = 0 := by
  simpa using contract_smul (φ := φ) (0 : K) (0 : Fin 3 ⊕ Fin 3 → K)

theorem spanAt_le_of_kleinLine_le (hσ : IsUnitaryInvolution σ) {c d : Frame σ 4}
    {S S' : Finset (Fin 4)} (hS : 2 ≤ S.card)
    (h : kleinLine (c.spanAt S) (c.spanAt S) ≤ kleinLine (d.spanAt S') (d.spanAt S')) :
    c.spanAt S ≤ d.spanAt S' := by
  rw [Frame.le_spanAt_iff hσ]
  intro l hl w hw u hu
  let φ : Fin 4 → K := fun i => σ (w i)
  have hφu : ∀ x : Fin 4 → K, φ ⬝ᵥ x = herm σ w x := fun x => rfl
  have hgen : ∀ x ∈ d.spanAt S', φ ⬝ᵥ x = 0 := by
    intro x hx
    rw [hφu]
    exact d.orth_spanAt hl w hw x hx
  have hcontr : ∀ y ∈ kleinLine (d.spanAt S') (d.spanAt S'), contract φ y = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => contract φ y = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨x, hx, z, hz, rfl⟩
      rw [contract_kleinWedge, hgen x hx, hgen z hz, zero_smul, zero_smul, add_zero]
    · exact contract_zero φ
    · intro a b _ _ ha hb
      rw [contract_add, ha, hb, add_zero]
    · intro a b _ hb
      rw [contract_smul, hb, smul_zero]
  have hkey : ∀ u ∈ c.spanAt S, φ ⬝ᵥ u = 0 := by
    intro u hu
    by_contra hu0
    have hAu : c.spanAt S ≤ K ∙ u := by
      intro v hv
      have hmem : kleinWedge u v ∈ kleinLine (c.spanAt S) (c.spanAt S) :=
        Submodule.subset_span ⟨u, hu, v, hv, rfl⟩
      have h0 : contract φ (kleinWedge u v) = 0 := hcontr _ (h hmem)
      rw [contract_kleinWedge] at h0
      have heq : (φ ⬝ᵥ u) • v = (φ ⬝ᵥ v) • u := CharTwo.add_eq_zero.mp h0
      refine Submodule.mem_span_singleton.mpr ⟨(φ ⬝ᵥ u)⁻¹ * (φ ⬝ᵥ v), ?_⟩
      calc ((φ ⬝ᵥ u)⁻¹ * (φ ⬝ᵥ v)) • u
          = (φ ⬝ᵥ u)⁻¹ • ((φ ⬝ᵥ v) • u) := by rw [smul_smul]
        _ = (φ ⬝ᵥ u)⁻¹ • ((φ ⬝ᵥ u) • v) := by rw [heq]
        _ = v := by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
    have hu_ne : u ≠ 0 := by
      rintro rfl
      exact hu0 (by simp [φ])
    have hle : Module.finrank K (c.spanAt S) ≤ 1 := by
      have hmono := Submodule.finrank_mono hAu
      rwa [finrank_span_singleton hu_ne] at hmono
    have hdim := c.finrank_spanAt S
    omega
  rw [← hφu]
  exact hkey u hu

omit [CharP K 2] in
theorem Frame.perp_spanAt_eq_line (hσ : IsUnitaryInvolution σ) {m : ℕ} {c : Frame σ m}
    {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) (hS : S.card = m - 1) :
    perp σ (c.spanAt S) = c.line k := by
  have hle : c.line k ≤ perp σ (c.spanAt S) := c.orth_spanAt hk
  have hdim : Module.finrank K (perp σ (c.spanAt S)) = 1 := by
    have hnd := c.nondeg_spanAt hσ S
    have hW := finrank_eq_add_finrank_inf_perp (σ := σ) (m := m) hσ hnd
      (le_top : c.spanAt S ≤ ⊤)
    rw [finrank_top, Module.finrank_fin_fun, top_inf_eq, c.finrank_spanAt, hS] at hW
    have hm : 1 ≤ m := Fin.pos k
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [c.finrank_line k, hdim])).symm

omit [CharP K 2] in
theorem Frame.line_eq_spanAt_inf_perp (hσ : IsUnitaryInvolution σ) {m : ℕ} {c : Frame σ m}
    {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) :
    c.line k = c.spanAt (insert k S) ⊓ perp σ (c.spanAt S) := by
  have hP : Nondeg σ (c.spanAt S) := c.nondeg_spanAt hσ S
  have hsplit : c.spanAt (insert k S) = c.spanAt S ⊔ c.line k := by
    rw [Frame.spanAt_insert, sup_comm]
  refine le_antisymm ?_ ?_
  · refine le_inf (Frame.line_le_spanAt (Finset.mem_insert_self _ _)) ?_
    exact c.orth_spanAt hk
  · intro x hx
    obtain ⟨hxU, hxP⟩ := Submodule.mem_inf.mp hx
    rw [hsplit] at hxU
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxU
    have hy0 : y = 0 := by
      refine hP y hy fun t ht => ?_
      have h2 := hxP t ht
      rw [herm_add_left, c.orth_spanAt hk z hz t ht, add_zero] at h2
      exact h2
    simpa [hy0] using hz

omit [CharP K 2] in
theorem Frame.line_eq_of_spanAt_eq (hσ : IsUnitaryInvolution σ) {c d : Frame σ 4} {i : Fin 3}
    (h : ∀ l : ℕ, l ≤ 4 → l ≠ (i : ℕ) + 1 →
      c.spanAt (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < l) =
      d.spanAt (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < l)) :
    ∀ k : Fin 4, k ≠ i.castSucc → k ≠ i.succ → c.line k = d.line k := by
  intro k hk1 hk2
  have hk_ne_i : (k : ℕ) ≠ (i : ℕ) := fun h' => hk1 (Fin.ext h')
  have hk_ne_succ : (k : ℕ) ≠ (i : ℕ) + 1 := fun h' => hk2 (Fin.ext (by simpa using h'))
  have hknot : k ∉ Finset.univ.filter (fun j : Fin 4 => (j : ℕ) < (k : ℕ)) := by simp
  have hins : (insert k (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < (k : ℕ))) =
      Finset.univ.filter fun j : Fin 4 => (j : ℕ) < (k : ℕ) + 1 := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | hj)
      · omega
      · omega
    · intro hj
      by_cases hjk : j = k
      · exact Or.inl hjk
      · refine Or.inr ?_
        have : (j : ℕ) ≠ (k : ℕ) := fun h' => hjk (Fin.ext h')
        omega
  have hone : c.spanAt (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < (k : ℕ) + 1) =
      d.spanAt (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < (k : ℕ) + 1) :=
    h ((k : ℕ) + 1) (by omega) fun hEq => hk_ne_i (by omega)
  have hzero : c.spanAt (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < (k : ℕ)) =
      d.spanAt (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < (k : ℕ)) :=
    h (k : ℕ) (by omega) hk_ne_succ
  rw [Frame.line_eq_spanAt_inf_perp hσ (c := c) hknot,
    Frame.line_eq_spanAt_inf_perp hσ (c := d) hknot, hins, hone, hzero]

@[expose] def kleinType : Fin 3 → Fin 3 := ![2, 0, 1]

theorem kleinType_surjective : Function.Surjective kleinType := by
  intro i
  fin_cases i
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨0, by decide⟩

private theorem line_zero_eq_of_star_eq (hσ : IsUnitaryInvolution σ) {c d : Frame σ 4}
    (h : kleinLine (c.line 0) (⊤ : Submodule K (Fin 4 → K)) =
      kleinLine (d.line 0) (⊤ : Submodule K (Fin 4 → K))) : c.line 0 = d.line 0 := by
  have hΛ : kleinLine (c.spanAt ({1, 2, 3} : Finset (Fin 4)))
        (c.spanAt ({1, 2, 3} : Finset (Fin 4))) =
      kleinLine (d.spanAt ({1, 2, 3} : Finset (Fin 4)))
        (d.spanAt ({1, 2, 3} : Finset (Fin 4))) := by
    rw [← dFlipSub_kleinLine_line_zero hσ c, ← dFlipSub_kleinLine_line_zero hσ d, h]
  have hspan : c.spanAt ({1, 2, 3} : Finset (Fin 4)) =
      d.spanAt ({1, 2, 3} : Finset (Fin 4)) := by
    refine le_antisymm ?_ ?_
    · exact spanAt_le_of_kleinLine_le hσ (S := {1, 2, 3}) (S' := {1, 2, 3}) (by decide)
        (le_of_eq hΛ)
    · exact spanAt_le_of_kleinLine_le hσ (S := {1, 2, 3}) (S' := {1, 2, 3}) (by decide)
        (le_of_eq hΛ.symm)
  rw [← Frame.perp_spanAt_eq_line hσ (c := c) (S := {1, 2, 3}) (k := 0) (by decide)
      (by decide),
    ← Frame.perp_spanAt_eq_line hσ (c := d) (S := {1, 2, 3}) (k := 0) (by decide)
      (by decide), hspan]

theorem adj_kleinChamber_iff (hσ : IsUnitaryInvolution σ) (i : Fin 3) {c d : Frame σ 4} :
    (dChamberSystem σ 2).adj (kleinType i) (kleinChamber hσ c) (kleinChamber hσ d) ↔
      (frameSystem σ 3).adj i c d := by
  constructor
  · intro h
    rw [dChamberSystem_adj_iff] at h
    fin_cases i
    · rw [frameSystem_adj]
      have hs2 : c.spanAt ({0, 1} : Finset (Fin 4)) = d.spanAt ({0, 1} : Finset (Fin 4)) := by
        have h0 : (kleinChamber hσ c).elt 0 = (kleinChamber hσ d).elt 0 := h 0 (by decide)
        rw [elt_kleinChamber_zero, elt_kleinChamber_zero] at h0
        exact le_antisymm
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1}) (S' := {0, 1}) (by decide) (le_of_eq h0))
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1}) (S' := {0, 1}) (by decide)
            (le_of_eq h0.symm))
      have hs3 : c.spanAt ({0, 1, 2} : Finset (Fin 4)) =
          d.spanAt ({0, 1, 2} : Finset (Fin 4)) := by
        have h1 : (kleinChamber hσ c).elt 1 = (kleinChamber hσ d).elt 1 := h 1 (by decide)
        rw [elt_kleinChamber_one, elt_kleinChamber_one] at h1
        exact le_antisymm
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1, 2}) (S' := {0, 1, 2}) (by decide)
            (le_of_eq h1))
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1, 2}) (S' := {0, 1, 2}) (by decide)
            (le_of_eq h1.symm))
      refine Frame.line_eq_of_spanAt_eq hσ ?_
      intro l hl hne
      interval_cases l
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 0) = ∅ by decide,
          Frame.spanAt_empty, Frame.spanAt_empty]
      · exact absurd rfl hne
      · exact hs2
      · exact hs3
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 4) = Finset.univ by decide,
          Frame.spanAt_univ hσ, Frame.spanAt_univ hσ]
    · rw [frameSystem_adj]
      have hs3 : c.spanAt ({0, 1, 2} : Finset (Fin 4)) =
          d.spanAt ({0, 1, 2} : Finset (Fin 4)) := by
        have h1 : (kleinChamber hσ c).elt 1 = (kleinChamber hσ d).elt 1 := h 1 (by decide)
        rw [elt_kleinChamber_one, elt_kleinChamber_one] at h1
        exact le_antisymm
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1, 2}) (S' := {0, 1, 2}) (by decide)
            (le_of_eq h1))
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1, 2}) (S' := {0, 1, 2}) (by decide)
            (le_of_eq h1.symm))
      have hstar : (kleinChamber hσ c).elt 2 = (kleinChamber hσ d).elt 2 := h 2 (by decide)
      rw [elt_kleinChamber_two, elt_kleinChamber_two] at hstar
      have hline0 := line_zero_eq_of_star_eq hσ hstar
      refine Frame.line_eq_of_spanAt_eq hσ ?_
      intro l hl hne
      interval_cases l
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 0) = ∅ by decide,
          Frame.spanAt_empty, Frame.spanAt_empty]
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 1) = {0} by decide,
          Frame.spanAt_singleton, Frame.spanAt_singleton, hline0]
      · exact absurd rfl hne
      · exact hs3
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 4) = Finset.univ by decide,
          Frame.spanAt_univ hσ, Frame.spanAt_univ hσ]
    · rw [frameSystem_adj]
      have hs2 : c.spanAt ({0, 1} : Finset (Fin 4)) = d.spanAt ({0, 1} : Finset (Fin 4)) := by
        have h0 : (kleinChamber hσ c).elt 0 = (kleinChamber hσ d).elt 0 := h 0 (by decide)
        rw [elt_kleinChamber_zero, elt_kleinChamber_zero] at h0
        exact le_antisymm
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1}) (S' := {0, 1}) (by decide) (le_of_eq h0))
          (spanAt_le_of_kleinLine_le hσ (S := {0, 1}) (S' := {0, 1}) (by decide)
            (le_of_eq h0.symm))
      have hstar : (kleinChamber hσ c).elt 2 = (kleinChamber hσ d).elt 2 := h 2 (by decide)
      rw [elt_kleinChamber_two, elt_kleinChamber_two] at hstar
      have hline0 := line_zero_eq_of_star_eq hσ hstar
      refine Frame.line_eq_of_spanAt_eq hσ ?_
      intro l hl hne
      interval_cases l
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 0) = ∅ by decide,
          Frame.spanAt_empty, Frame.spanAt_empty]
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 1) = {0} by decide,
          Frame.spanAt_singleton, Frame.spanAt_singleton, hline0]
      · exact hs2
      · exact absurd rfl hne
      · rw [show (Finset.univ.filter fun j : Fin 4 => (j : ℕ) < 4) = Finset.univ by decide,
          Frame.spanAt_univ hσ, Frame.spanAt_univ hσ]
  · intro h
    rw [frameSystem_adj] at h
    rw [dChamberSystem_adj_iff]
    fin_cases i
    · have h01 : c.spanAt ({0, 1} : Finset (Fin 4)) = d.spanAt ({0, 1} : Finset (Fin 4)) := by
        refine Frame.spanAt_eq_of_agree hσ ?_
        intro k hk
        exact h k (by fin_cases k <;> simp_all) (by fin_cases k <;> simp_all)
      have h012 : c.spanAt ({0, 1, 2} : Finset (Fin 4)) =
          d.spanAt ({0, 1, 2} : Finset (Fin 4)) := by
        refine Frame.spanAt_eq_of_agree hσ ?_
        intro k hk
        exact h k (by fin_cases k <;> simp_all) (by fin_cases k <;> simp_all)
      intro j hj
      fin_cases j
      · change (kleinChamber hσ c).elt 0 = (kleinChamber hσ d).elt 0
        rw [elt_kleinChamber_zero, elt_kleinChamber_zero, h01]
      · change (kleinChamber hσ c).elt 1 = (kleinChamber hσ d).elt 1
        rw [elt_kleinChamber_one, elt_kleinChamber_one, h012]
      · exact absurd hj (by decide)
    · have h012 : c.spanAt ({0, 1, 2} : Finset (Fin 4)) =
          d.spanAt ({0, 1, 2} : Finset (Fin 4)) := by
        refine Frame.spanAt_eq_of_agree hσ ?_
        intro k hk
        exact h k (by fin_cases k <;> simp_all) (by fin_cases k <;> simp_all)
      have hline0 : c.line 0 = d.line 0 := h 0 (by decide) (by decide)
      intro j hj
      fin_cases j
      · exact absurd hj (by decide)
      · change (kleinChamber hσ c).elt 1 = (kleinChamber hσ d).elt 1
        rw [elt_kleinChamber_one, elt_kleinChamber_one, h012]
      · change (kleinChamber hσ c).elt 2 = (kleinChamber hσ d).elt 2
        rw [elt_kleinChamber_two, elt_kleinChamber_two, hline0]
    · have hline0 : c.line 0 = d.line 0 := h 0 (by decide) (by decide)
      have hline1 : c.line 1 = d.line 1 := h 1 (by decide) (by decide)
      have h01 : c.spanAt ({0, 1} : Finset (Fin 4)) = d.spanAt ({0, 1} : Finset (Fin 4)) := by
        rw [Frame.spanAt_pair, Frame.spanAt_pair, hline0, hline1]
      intro j hj
      fin_cases j
      · change (kleinChamber hσ c).elt 0 = (kleinChamber hσ d).elt 0
        rw [elt_kleinChamber_zero, elt_kleinChamber_zero, h01]
      · exact absurd hj (by decide)
      · change (kleinChamber hσ c).elt 2 = (kleinChamber hσ d).elt 2
        rw [elt_kleinChamber_two, elt_kleinChamber_two, hline0]

theorem kleinChamber_injective (hσ : IsUnitaryInvolution σ) :
    Function.Injective (kleinChamber hσ) := by
  intro c d hcd
  have h0 := congrArg (fun x : DChamber σ 3 => x.elt 0) hcd
  have h1 := congrArg (fun x : DChamber σ 3 => x.elt 1) hcd
  have h2 := congrArg (fun x : DChamber σ 3 => x.elt 2) hcd
  rw [elt_kleinChamber_zero, elt_kleinChamber_zero] at h0
  rw [elt_kleinChamber_one, elt_kleinChamber_one] at h1
  rw [elt_kleinChamber_two, elt_kleinChamber_two] at h2
  have h01 : c.spanAt ({0, 1} : Finset (Fin 4)) = d.spanAt ({0, 1} : Finset (Fin 4)) :=
    le_antisymm
      (spanAt_le_of_kleinLine_le hσ (S := {0, 1}) (S' := {0, 1}) (by decide) (le_of_eq h0))
      (spanAt_le_of_kleinLine_le hσ (S := {0, 1}) (S' := {0, 1}) (by decide)
        (le_of_eq h0.symm))
  have h012 : c.spanAt ({0, 1, 2} : Finset (Fin 4)) =
      d.spanAt ({0, 1, 2} : Finset (Fin 4)) :=
    le_antisymm
      (spanAt_le_of_kleinLine_le hσ (S := {0, 1, 2}) (S' := {0, 1, 2}) (by decide)
        (le_of_eq h1))
      (spanAt_le_of_kleinLine_le hσ (S := {0, 1, 2}) (S' := {0, 1, 2}) (by decide)
        (le_of_eq h1.symm))
  have hl0 : c.line 0 = d.line 0 := line_zero_eq_of_star_eq hσ h2
  apply Frame.ext
  funext k
  fin_cases k
  · exact hl0
  · change c.line 1 = d.line 1
    rw [Frame.line_eq_spanAt_inf_perp hσ (c := c) (S := {0}) (k := 1) (by decide),
      Frame.line_eq_spanAt_inf_perp hσ (c := d) (S := {0}) (k := 1) (by decide),
      show (insert 1 ({0} : Finset (Fin 4))) = ({0, 1} : Finset (Fin 4)) by decide,
      Frame.spanAt_singleton, Frame.spanAt_singleton, hl0, h01]
  · change c.line 2 = d.line 2
    rw [Frame.line_eq_spanAt_inf_perp hσ (c := c) (S := {0, 1}) (k := 2) (by decide),
      Frame.line_eq_spanAt_inf_perp hσ (c := d) (S := {0, 1}) (k := 2) (by decide),
      show (insert 2 ({0, 1} : Finset (Fin 4))) = ({0, 1, 2} : Finset (Fin 4)) by decide,
      h012, h01]
  · change c.line 3 = d.line 3
    rw [← Frame.perp_spanAt_eq_line hσ (c := c) (S := {0, 1, 2}) (k := 3) (by decide)
        (by decide),
      ← Frame.perp_spanAt_eq_line hσ (c := d) (S := {0, 1, 2}) (k := 3) (by decide)
        (by decide), h012]

theorem kleinChamber_surjective (hσ : IsUnitaryInvolution σ) [Finite K] :
    Function.Surjective (kleinChamber hσ) := by
  intro D
  have hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a := by
    intro a ha ha0
    obtain ⟨x, hx⟩ := hσ.norm_surj a ha ha0
    exact ⟨x, by rw [mul_comm]; exact hx⟩
  obtain ⟨L, hL_Q, hL_flip, hline⟩ := D.toFlipFrame.exists_isometry hσ.invol hN
  have hLmem : L ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 3 K) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro y
    exact hL_Q y
  have hspan : D.spanAt Finset.univ = (stdLag 3 K).map L.toLinearMap := by
    rw [FlipFrame.spanAt, Finset.sup_univ_eq_iSup]
    have hline' : ∀ i : Fin 3, D.line i = K ∙ L (stdE (K := K) (n := 3) i) := by
      intro i
      rw [← hline i, Submodule.map_span, Set.image_singleton]
      rfl
    have hsup : (⨆ i : Fin 3, D.line i) =
        ⨆ i : Fin 3, K ∙ L (stdE (K := K) (n := 3) i) := iSup_congr hline'
    rw [hsup, ← Submodule.span_range_eq_iSup, stdLag_eq_span_stdE, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨stdE (K := K) (n := 3) j, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  have hD : kleinDickson (K := K) ⟨L, hLmem⟩ = 1 := by
    refine (kleinDickson_eq_one_iff (K := K) ⟨L, hLmem⟩).mpr ?_
    rw [← hspan]
    exact D.even_ruling
  obtain ⟨g, hg⟩ := exists_rho_eq (K := K) ⟨L, hLmem⟩ hD
  have hcomm : ∀ w, Klein.rho g (dFlip σ w) = dFlip σ (Klein.rho g w) := by
    intro w
    rw [hg]
    exact hL_flip w
  obtain ⟨u, hu⟩ := exists_SUid_of_rho_comm hσ.invol g hcomm
  refine ⟨u • stdFrame σ 4, ?_⟩
  apply DChamber.ext
  funext j
  rw [kleinChamber_line_smul, kleinChamber_stdFrame, hu]
  rw [show Klein.cong (g : Matrix (Fin 4) (Fin 4) K) = (Klein.rho g).toLinearMap from rfl]
  rw [hg]
  exact hline j

theorem connected_dChamberSystem_two (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q) : (dChamberSystem σ 2).Connected :=
  CFSG.ClassicalInvolution.PhanG.connected_of_isTypeMorphism
    (X := frameSystem σ 3) (Y := dChamberSystem σ 2) (τ := kleinType)
    (f := kleinChamber hσ) (fun i _ _ h => (adj_kleinChamber_iff hσ i).mpr h)
    (kleinChamber_surjective hσ) (frameSystem_connected hσ hK hq)

theorem simplyTwoConnected_dChamberSystem_two (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) : (dChamberSystem σ 2).SimplyTwoConnected :=
  CFSG.ClassicalInvolution.PhanG.simplyTwoConnected_of_isPanelLift
    (X := frameSystem σ 3) (Y := dChamberSystem σ 2) (τ := kleinType)
    (f := kleinChamber hσ) (fun i _ _ h => (adj_kleinChamber_iff hσ i).mpr h)
    (by
      intro i x d h
      obtain ⟨y, hy⟩ := kleinChamber_surjective hσ d
      exact ⟨y, (adj_kleinChamber_iff hσ i).mp (hy ▸ h), hy⟩)
    (kleinChamber_injective hσ) (frameSystem_simplyTwoConnected hσ hK hq 3)
    kleinType_surjective (kleinChamber_surjective hσ)

end CFSG.ClassicalInvolution.PhanDn

end
