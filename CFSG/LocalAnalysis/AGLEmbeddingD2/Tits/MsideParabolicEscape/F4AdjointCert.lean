module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4AdjointModel

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4Adjoint

open CFSG.Blueprint.Chevalley Module

@[expose] def xTabData : List (List (List ℕ)) :=
  [[[0], [1, 4], [2], [3], [4], [5, 9], [6], [7], [8, 0, 4], [9], [10], [11, 17], [12, 20], [13], [14], [15], [16, 10], [17], [18], [19, 26], [20], [21, 28], [22], [23], [24, 18], [25], [26], [27], [28], [29, 35], [30, 22], [31], [32], [33, 27], [34], [35], [36, 31], [37], [38], [39], [40], [41, 37], [42], [43, 47], [44], [45], [46], [47], [48], [49], [50, 46], [51]],
  [[0, 5], [1], [2], [3], [4, 9], [5], [6, 12], [7], [8], [9], [10, 1, 5], [11], [12], [13], [14, 21], [15], [16, 8], [17, 25], [18], [19], [20], [21], [22, 13], [23], [24], [25], [26, 34], [27], [28], [29], [30], [31, 23], [32, 24], [33], [34], [35, 40], [36], [37], [38, 33], [39, 43], [40], [41], [42], [43], [44], [45, 41], [46, 42], [47], [48], [49], [50], [51]],
  [[0], [1, 6], [2], [3, 6], [4], [5, 12, 11], [6], [7, 14], [8], [9, 20, 17], [10], [11], [12], [13, 2, 6], [14], [15], [16], [17], [18, 22, 10], [19], [20], [21, 29], [22], [23, 15], [24, 30, 16], [25], [26], [27], [28, 35], [29], [30], [31], [32], [33], [34, 48, 39], [35], [36], [37, 31], [38], [39], [40, 44], [41, 36], [42, 51, 38], [43], [44], [45], [46], [47], [48], [49, 45], [50], [51]],
  [[0], [1], [2, 7], [3], [4], [5], [6, 14], [7], [8], [9], [10], [11, 29, 19], [12, 21], [13], [14], [15, 3, 7], [16], [17, 35, 26], [18], [19], [20, 28], [21], [22], [23, 13], [24], [25, 40, 34], [26], [27, 37, 18], [28], [29], [30], [31, 22], [32], [33, 41, 24], [34], [35], [36, 30], [37], [38, 45, 32], [39], [40], [41], [42], [43], [44, 48], [45], [46], [47], [48], [49], [50], [51, 49]]]

@[expose] def yTabData : List (List (List ℕ)) :=
  [[[0], [1, 8], [2], [3], [4, 0, 8], [5], [6], [7], [8], [9, 5], [10, 16], [11], [12], [13], [14], [15], [16], [17, 11], [18, 24], [19], [20, 12], [21], [22, 30], [23], [24], [25], [26, 19], [27, 33], [28, 21], [29], [30], [31, 36], [32], [33], [34], [35, 29], [36], [37, 41], [38], [39], [40], [41], [42], [43], [44], [45], [46, 50], [47, 43], [48], [49], [50], [51]],
  [[0, 10], [1], [2], [3], [4], [5, 1, 10], [6], [7], [8, 16], [9, 4], [10], [11], [12, 6], [13, 22], [14], [15], [16], [17], [18], [19], [20], [21, 14], [22], [23, 31], [24, 32], [25, 17], [26], [27], [28], [29], [30], [31], [32], [33, 38], [34, 26], [35], [36], [37], [38], [39], [40, 35], [41, 45], [42, 46], [43, 39], [44], [45], [46], [47], [48], [49], [50], [51]],
  [[0], [1, 13], [2], [3, 13], [4], [5], [6, 2, 13], [7], [8], [9], [10, 22, 18], [11, 12, 5], [12], [13], [14, 7], [15, 23], [16, 30, 24], [17, 20, 9], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28], [29, 21], [30], [31, 37], [32], [33], [34], [35, 28], [36, 41], [37], [38, 51, 42], [39, 48, 34], [40], [41], [42], [43], [44, 40], [45, 49], [46], [47], [48], [49], [50], [51]],
  [[0], [1], [2, 15], [3], [4], [5], [6], [7, 3, 15], [8], [9], [10], [11], [12], [13, 23], [14, 6], [15], [16], [17], [18, 37, 27], [19, 29, 11], [20], [21, 12], [22, 31], [23], [24, 41, 33], [25], [26, 35, 17], [27], [28, 20], [29], [30, 36], [31], [32, 45, 38], [33], [34, 40, 25], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [46], [47], [48, 44], [49, 51], [50], [51]]]

@[expose] def xTab (i b : ℕ) : List ℕ := (xTabData.getD i []).getD b []

@[expose] def yTab (i b : ℕ) : List ℕ := (yTabData.getD i []).getD b []

@[expose] def applyX (i : ℕ) (L : List ℕ) : List ℕ := L.flatMap (xTab i)

@[expose] def applyY (i : ℕ) (L : List ℕ) : List ℕ := L.flatMap (yTab i)


theorem xCol_eq_tab : ∀ i : Fin Tag.F4.rank, ∀ b < 52, xCol i b = xTab i b := by decide +kernel

theorem yCol_eq_tab : ∀ i : Fin Tag.F4.rank, ∀ b < 52, yCol i b = yTab i b := by decide +kernel


theorem xTab_lt : ∀ i : Fin Tag.F4.rank, ∀ b < 52, ∀ l ∈ xTab i b, l < 52 := by decide +kernel

theorem yTab_lt : ∀ i : Fin Tag.F4.rank, ∀ b < 52, ∀ l ∈ yTab i b, l < 52 := by decide +kernel

variable {R : Type*} [CommRing R] [CharP R 2]

theorem xOp_one_lvec (i : Fin Tag.F4.rank) {L : List ℕ} (hL : ∀ l ∈ L, l < 52) :
    xOp Tag.F4 R i 1 (lvec R L) = lvec R (applyX i L) := by
  induction L with
  | nil => simp [lvec_nil, applyX]
  | cons b L ih =>
    have hb : b < 52 := hL b List.mem_cons_self
    have e : applyX i (b :: L) = xTab i b ++ applyX i L := List.flatMap_cons
    rw [lvec_cons, map_add, ih fun l h => hL l (List.mem_cons_of_mem _ h),
      toVec_one_shiftLeft' hb, xOp_one_single i ⟨b, hb⟩, xCol_eq_tab i b hb, e, lvec_append]

theorem yOp_one_lvec (i : Fin Tag.F4.rank) {L : List ℕ} (hL : ∀ l ∈ L, l < 52) :
    yOp Tag.F4 R i 1 (lvec R L) = lvec R (applyY i L) := by
  induction L with
  | nil => simp [lvec_nil, applyY]
  | cons b L ih =>
    have hb : b < 52 := hL b List.mem_cons_self
    have e : applyY i (b :: L) = yTab i b ++ applyY i L := List.flatMap_cons
    rw [lvec_cons, map_add, ih fun l h => hL l (List.mem_cons_of_mem _ h),
      toVec_one_shiftLeft' hb, yOp_one_single i ⟨b, hb⟩, yCol_eq_tab i b hb, e, lvec_append]

theorem applyX_lt (i : Fin Tag.F4.rank) {L : List ℕ} (hL : ∀ l ∈ L, l < 52) :
    ∀ l ∈ applyX i L, l < 52 := by
  intro l hl
  obtain ⟨b, hb, hl⟩ := List.mem_flatMap.1 hl
  exact xTab_lt i b (hL b hb) l hl

theorem applyY_lt (i : Fin Tag.F4.rank) {L : List ℕ} (hL : ∀ l ∈ L, l < 52) :
    ∀ l ∈ applyY i L, l < 52 := by
  intro l hl
  obtain ⟨b, hb, hl⟩ := List.mem_flatMap.1 hl
  exact yTab_lt i b (hL b hb) l hl

theorem sub_one_lvec {f : Module.End R (RootModule Tag.F4 R)} {fIdx : List ℕ → List ℕ}
    {L : List ℕ} (hf : f (lvec R L) = lvec R (fIdx L)) :
    (f - 1) (lvec R L) = lvec R (L ++ fIdx L) := by
  have hneg : -lvec R L = lvec R L := by
    ext l
    rw [Finsupp.neg_apply, CharTwo.neg_eq]
  rw [LinearMap.sub_apply, hf, Module.End.one_apply, sub_eq_add_neg, hneg, lvec_append, add_comm]

@[expose] def certOK (fIdx : List ℕ → List ℕ) (piv : List ℕ) (pre : List (List ℕ))
    (zs : List ℕ) : Bool :=
  (pre.length == piv.length && zs == pre.map fun s => idxMask (fIdx s)) &&
  ((piv.all fun p => decide (p < 52)) && pre.all fun s => s.all fun l => decide (l < 52)) &&
  ((List.range piv.length).all fun j => (List.range piv.length).all fun k =>
    (zs.getD j 0).testBit (piv.getD k 0) == (j == k)) &&
  (List.range 52).all fun b =>
    idxMask (fIdx [b]) == xorMap (fun k => zs.getD k 0)
      ((List.range piv.length).filter fun k => (idxMask (fIdx [b])).testBit (piv.getD k 0))

theorem list_sum_mem_span {M : Type*} [AddCommGroup M] [Module R M] {s : Set M} :
    ∀ L : List M, (∀ x ∈ L, x ∈ s) → L.sum ∈ Submodule.span R s
  | [], _ => by simp
  | x :: L, h => by
    rw [List.sum_cons]
    exact add_mem (Submodule.subset_span (h x List.mem_cons_self))
      (list_sum_mem_span L fun y hy => h y (List.mem_cons_of_mem _ hy))


section Field

variable {R : Type*} [Field R] [CharP R 2]

theorem finrank_range_of_certOK
    (f : Module.End R (RootModule Tag.F4 R)) (fIdx : List ℕ → List ℕ)
    (hf : ∀ L : List ℕ, (∀ l ∈ L, l < 52) → f (lvec R L) = lvec R (fIdx L))
    (piv : List ℕ) (pre : List (List ℕ)) (zs : List ℕ) (h : certOK fIdx piv pre zs = true) :
    finrank R (LinearMap.range f) = piv.length := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hlen, hzs⟩, hpiv, hpre⟩, hdiag⟩, hcol⟩ := h
  set r := piv.length
  have hzk : ∀ k : Fin r, zs.getD k 0 = idxMask (fIdx (pre.getD k [])) := by
    intro k
    rw [hzs, List.getD_eq_getElem _ _ (by rw [List.length_map, hlen]; exact k.2),
      List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2), List.getElem_map]
  have hpk : ∀ k : Fin r, piv.getD k 0 < 52 := fun k => by
    rw [List.getD_eq_getElem _ _ k.2]
    exact hpiv _ (List.getElem_mem _)
  let z : Fin r → RootModule Tag.F4 R := fun k => toVec R (zs.getD k 0)
  have hz : ∀ k, z k = f (lvec R (pre.getD k [])) := by
    intro k
    have hmem : pre.getD k [] ∈ pre := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact k.2)]
      exact List.getElem_mem _
    change toVec R (zs.getD k 0) = _
    rw [hzk, toVec_idxMask, hf _ (hpre _ hmem)]
  have hli : LinearIndependent R z := by
    refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
    have h1 := congrArg (fun v : RootModule Tag.F4 R => v (lab ⟨_, hpk k⟩)) hg
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply, z, toVec_apply_lab] at h1
    rw [Finset.sum_eq_single k] at h1
    · rw [hdiag k k.2 k k.2, beq_self_eq_true] at h1
      simpa using h1
    · intro j _ hj
      rw [hdiag j j.2 k k.2]
      have : (j : ℕ) ≠ k := fun e => hj (Fin.ext e)
      simp [this]
    · simp
  have hrange : LinearMap.range f = Submodule.span R (Set.range z) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨v, rfl⟩
      induction v using Finsupp.induction_linear with
      | zero => rw [map_zero]; exact zero_mem _
      | add a b ha hb => rw [map_add]; exact add_mem ha hb
      | single l c =>
        obtain ⟨b, rfl⟩ := lab_surjective l
        have hc : Finsupp.single (lab b) c = c • Finsupp.single (lab b) (1 : R) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hc, map_smul]
        refine Submodule.smul_mem _ _ ?_
        rw [← lvec_singleton b.2, hf _ (by simp), ← toVec_idxMask, hcol b b.2, toVec_xorMap]
        refine list_sum_mem_span _ fun x hx => ?_
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        exact ⟨⟨k, (List.mem_range.1 (List.mem_filter.1 hk).1)⟩, rfl⟩
    · rintro _ ⟨k, rfl⟩
      rw [hz]
      exact LinearMap.mem_range_self _ _
  rw [hrange, finrank_span_eq_card hli, Fintype.card_fin]

end Field

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4Adjoint
