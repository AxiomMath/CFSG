module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.OrbitData
import CFSG.Sporadic.ThSchreier.BFS

public section

namespace CFSG.KC.ThBfs

open CFSG.EvenSporadicStandard.ThStd.LocalDataTh CFSG.Sporadic.LySchreier
open scoped Matrix

theorem foldl_xor_lt16 (cs : List ℕ) (hcs : ∀ x ∈ cs, x < 16) (v : ℕ) (l : List ℕ) (a : ℕ)
    (ha : a < 16) :
    l.foldl (fun acc j => if v.testBit j then acc ^^^ cs.getD j 0 else acc) a < 16 := by
  induction l generalizing a with
  | nil => exact ha
  | cons j l ih =>
    refine ih _ ?_
    change (if v.testBit j = true then a ^^^ cs.getD j 0 else a) < 16
    by_cases hj : v.testBit j = true
    · rw [ite_eq_left hj]
      have hc : cs.getD j 0 < 16 := by
        rw [List.getD_eq_getElem?_getD]
        rcases h : cs[j]? with _ | c
        · simp
        · exact hcs c (List.mem_of_getElem? h)
      exact Nat.xor_lt_two_pow (n := 4) ha hc
    · rw [ite_eq_right hj]
      exact ha

theorem applyCols_lt16 {a : List ℕ} (ha : ∀ x ∈ a, x < 16) (v : ℕ) : applyCols 4 a v < 16 :=
  foldl_xor_lt16 a ha v _ 0 (by norm_num)

theorem mem_allMat4_of_lt {cs : List ℕ} (hl : cs.length = 4) (hlt : ∀ x ∈ cs, x < 16) :
    cs ∈ allMat4 := by
  match cs, hl with
  | [a, b, c, d], _ =>
    simp only [allMat4, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨a, hlt a (by simp), b, hlt b (by simp), c, hlt c (by simp), d, hlt d (by simp), rfl⟩

theorem exists_of_mem_allMat4 {cs : List ℕ} (h : cs ∈ allMat4) :
    ∃ a < 16, ∃ b < 16, ∃ c < 16, ∃ d < 16, cs = [a, b, c, d] := by
  simp only [allMat4, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
  exact ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩

theorem lt16_of_mem_allMat4 {cs : List ℕ} (h : cs ∈ allMat4) : ∀ x ∈ cs, x < 16 := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := exists_of_mem_allMat4 h
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

theorem mulCols_mem {a cs : List ℕ} (ha : ∀ x ∈ a, x < 16) : mulCols 4 a cs ∈ allMat4 := by
  have h : mulCols 4 a cs = [applyCols 4 a (cs.getD 0 0), applyCols 4 a (cs.getD 1 0),
      applyCols 4 a (cs.getD 2 0), applyCols 4 a (cs.getD 3 0)] := rfl
  rw [h]
  refine mem_allMat4_of_lt rfl fun x hx => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact applyCols_lt16 ha _

theorem lt16_pow (c : ℕ) (hc : c < 16) : c < 2 ^ 4 := lt_of_lt_of_eq hc (by norm_num)

theorem codeVec4_eq_zero {c : ℕ} (hc : c < 16) (h : codeVec 4 c = 0) : c = 0 :=
  codeVec_injOn 4 (lt16_pow c hc) (lt16_pow 0 (by norm_num)) (h.trans (codeVec_zero 4).symm)

theorem det_ne_zero_of_invCode {cs : List ℕ} (hcs : cs ∈ allMat4) (h : invCode cs = true) :
    (matOfCols 4 cs).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨c, hc, rfl⟩ := exists_codeVec 4 v
  have hc' : c < 16 := lt_of_lt_of_eq hc (by norm_num)
  rw [matOfCols_mulVec] at hMv
  have h0 := codeVec4_eq_zero (applyCols_lt16 (lt16_of_mem_allMat4 hcs) c) hMv
  have hc0 : c ≠ 0 := fun e => hv (by rw [e, codeVec_zero])
  unfold invCode at h
  have h1 := List.all_eq_true.1 h (c - 1) (List.mem_range.2 (by omega))
  rw [Nat.sub_add_cancel (by omega), h0] at h1
  exact absurd h1 (by decide)

theorem invCode_of_det_ne_zero {cs : List ℕ} (hdet : (matOfCols 4 cs).det ≠ 0) :
    invCode cs = true := by
  unfold invCode
  rw [List.all_eq_true]
  intro s hs
  rw [List.mem_range] at hs
  rw [bne_iff_ne]
  intro h0
  apply hdet
  apply Matrix.exists_mulVec_eq_zero_iff.1
  refine ⟨codeVec 4 (s + 1), fun h => ?_, by rw [matOfCols_mulVec, h0, codeVec_zero]⟩
  have := codeVec4_eq_zero (c := s + 1) (by omega) h
  omega

theorem matOfCols_inj {a b : List ℕ} (ha : a ∈ allMat4) (hb : b ∈ allMat4)
    (h : matOfCols 4 a = matOfCols 4 b) : a = b := by
  have hcol : ∀ j : Fin 4, codeVec 4 (a.getD j 0) = codeVec 4 (b.getD j 0) := fun j => by
    funext i
    exact congrFun (congrFun h i) j
  have e : ∀ x y : ℕ, x < 16 → y < 16 → codeVec 4 x = codeVec 4 y → x = y :=
    fun x y hx hy hxy => codeVec_injOn 4 (lt16_pow x hx) (lt16_pow y hy) hxy
  obtain ⟨a0, h0, a1, h1, a2, h2, a3, h3, rfl⟩ := exists_of_mem_allMat4 ha
  obtain ⟨b0, g0, b1, g1, b2, g2, b3, g3, rfl⟩ := exists_of_mem_allMat4 hb
  rw [e a0 b0 h0 g0 (hcol 0), e a1 b1 h1 g1 (hcol 1), e a2 b2 h2 g2 (hcol 2),
    e a3 b3 h3 g3 (hcol 3)]

theorem card_inv_le : (allMat4.toFinset.filter fun cs => invCode cs = true).card ≤ 20160 := by
  set S := allMat4.toFinset.filter fun cs => invCode cs = true
  have hmem : ∀ cs ∈ S, cs ∈ allMat4 ∧ invCode cs = true := fun cs h => by
    simpa [S] using h
  have hu : ∀ cs ∈ S, IsUnit (matOfCols 4 cs) := fun cs h =>
    (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (det_ne_zero_of_invCode (hmem cs h).1 (hmem cs h).2))
  let f : S → GL (Fin 4) (ZMod 2) := fun x => (hu x.1 x.2).unit
  have hf : Function.Injective f := fun x y hxy => by
    have h := congrArg Units.val hxy
    simp only [f, IsUnit.unit_spec] at h
    exact Subtype.ext (matOfCols_inj (hmem _ x.2).1 (hmem _ y.2).1 h)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard, Matrix.card_GL_field] at h1
  simpa [Fin.prod_univ_four, ZMod.card] using h1

@[expose] def colW : List (List ℕ) :=
  [[1, 2, 4, 8], [2, 1, 4, 8], [3, 2, 4, 8], [4, 1, 2, 8], [5, 2, 4, 8], [6, 1, 4, 8], [7, 2, 4, 8],
    [8, 1, 2, 4], [9, 2, 4, 8], [10, 1, 4, 8], [11, 2, 4, 8], [12, 1, 2, 8], [13, 2, 4, 8],
    [14, 1, 4, 8], [15, 2, 4, 8]]

theorem colW_ok : ∀ s < 15, (colW.getD s []).length = 4 ∧ (∀ x ∈ colW.getD s [], x < 16) ∧
    invCode (colW.getD s []) = true ∧ (colW.getD s []).getD 0 0 = s + 1 := by
  decide

theorem gen_ok : ∀ T ∈ [T1c, T2c], (∀ x ∈ T, x < 16) ∧ T.length = 4 ∧ invCode T = true := by
  decide

theorem glList_sub : ∀ cs ∈ glList, cs ∈ allMat4 ∧ invCode cs = true := by
  intro cs hcs
  rw [glList] at hcs
  refine CFSG.Sporadic.ThSchreier.bfsList_mem_of_closed
    (S := {cs | cs ∈ allMat4 ∧ invCode cs = true}) [mulCols 4 T1c, mulCols 4 T2c] (idCols 4)
    ⟨mem_allMat4_of_lt rfl (by decide), by decide⟩ ?_ 20160 cs hcs
  intro g hg x hx
  have key : ∀ T ∈ [T1c, T2c], mulCols 4 T x ∈ {cs | cs ∈ allMat4 ∧ invCode cs = true} := by
    intro T hT
    obtain ⟨hlt, hl, hinv⟩ := gen_ok T hT
    refine ⟨mulCols_mem hlt, invCode_of_det_ne_zero ?_⟩
    rw [matOfCols_mulCols, Matrix.det_mul]
    exact mul_ne_zero (det_ne_zero_of_invCode (mem_allMat4_of_lt hl hlt) hinv)
      (det_ne_zero_of_invCode hx.1 hx.2)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact key T1c (by simp)
  · exact key T2c (by simp)

theorem glFacts_of_length (hlen : glList.length = 20160) : GLFacts = true := by
  have hnd : glList.Nodup :=
    CFSG.Sporadic.ThSchreier.bfsList_nodup [mulCols 4 T1c, mulCols 4 T2c] (idCols 4) 20160
  set S := allMat4.toFinset.filter fun cs => invCode cs = true
  have hsubF : glList.toFinset ⊆ S := fun cs h => by
    have := glList_sub cs (List.mem_toFinset.1 h)
    simp only [S, Finset.mem_filter, List.mem_toFinset]
    exact this
  have hcardG : glList.toFinset.card = 20160 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq : glList.toFinset = S :=
    Finset.eq_of_subset_of_card_le hsubF (by rw [hcardG]; exact card_inv_le)
  have hinv : ∀ cs ∈ allMat4, invCode cs = true → cs ∈ glList := fun cs h1 h2 => by
    have h : cs ∈ S := by
      simp only [S, Finset.mem_filter, List.mem_toFinset]
      exact ⟨h1, h2⟩
    rw [← heq] at h
    exact List.mem_toFinset.1 h
  change ((glList.length == 20160 && allMat4.all (fun cs => !invCode cs || glList.contains cs)) &&
      (List.range 15).all fun s => glList.any fun cs => cs.getD 0 0 == s + 1) = true
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.all_eq_true]
  refine ⟨⟨hlen, fun cs hcs => ?_⟩, fun s hs => ?_⟩
  · rw [Bool.or_eq_true]
    by_cases h : invCode cs = true
    · exact Or.inr (List.contains_iff_mem.2 (hinv cs hcs h))
    · left
      simpa using h
  · rw [List.mem_range] at hs
    obtain ⟨h1, h2, h3, h4⟩ := colW_ok s hs
    rw [List.any_eq_true]
    exact ⟨_, hinv _ (mem_allMat4_of_lt h1 h2) h3, beq_iff_eq.2 h4⟩

end CFSG.KC.ThBfs

end
