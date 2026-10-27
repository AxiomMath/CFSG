module

public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableRelations
public import Batteries.Data.ByteArray

public section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

@[expose] def walkRootC (L : ℕ) (tab fwd : ByteArray) (fuel : ℕ) : ℕ → List ℕ → Option ℕ
  | c, [] => some (findC fwd fuel c)
  | c, y :: w =>
    let d := getWord tab (findC fwd fuel c * L + y)
    if d = 0 then none else walkRootC L tab fwd fuel d w

theorem walkRootC_eq (L : ℕ) (tab fwd : ByteArray) (fuel : ℕ) :
    ∀ (w : List ℕ) (c : ℕ), walkRootC L tab fwd fuel c w =
      walkRoot L (wordsToArray tab) (linksToArray fwd) fuel c w := by
  intro w
  induction w with
  | nil => intro c; simp only [walkRootC, walkRoot, findC_eq]
  | cons y w ih =>
    intro c
    simp only [walkRootC, walkRoot, findC_eq, getD_wordsToArray]
    split
    · rfl
    · exact ih _

variable {m : ℕ}

theorem index_le_of_subsetCheckCC (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    (h : subsetCheckCC ws S cap n = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index ≤ n :=
  index_le_of_check (goodColParams ws _ _ (genSub_words_mem ws (subsetOf m S)))
    (by simpa [colParams, mkParams] using closure_colLetter ws)
    (subsetCheckC_of_subsetCheckCC ws S h)

@[expose] def subsetWalkCC (ws : List (List (Fin m × Bool))) (S : List ℕ) (cap n : ℕ)
    (us : List (List (Fin m × Bool))) : Bool :=
  decide ((cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) &&
    (let P := colParams ws ((subsetOf m S).map fun x => [(x, true)])
     let st := enumerateC P cap
     (!st.overflow && st.completeC P.L && st.liveCountC == n) &&
       (colCodes ws us).all fun w => walkRootC P.L st.tab st.fwd st.next 1 w == some 1)

theorem subsetWalkCC_sound (ws : List (List (Fin m × Bool))) (S : List ℕ) {cap n : ℕ}
    {us : List (List (Fin m × Bool))} (h : subsetWalkCC ws S cap n us = true) :
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S)).index ≤ n ∧
    ∀ u ∈ us, PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (FreeGroup.mk u) ∈
        genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S) := by
  unfold subsetWalkCC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcap, hchk, hwalk⟩ := h
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set H := genSub rels (subsetOf m S)
  set P := colParams ws ((subsetOf m S).map fun x => [(x, true)]) with hPdef
  have hL : P.L = (cols ws).length := rfl
  have hcap' : (cap + 2) * (P.L + 1) ≤ 2 ^ 32 := by rw [hL]; exact hcap
  have hg : Good (colLetter ws) H P := goodColParams ws _ H (genSub_words_mem ws (subsetOf m S))
  have hgen : Subgroup.closure (colLetter ws '' Set.Iio P.L) = ⊤ := by
    rw [hL]; exact closure_colLetter ws
  have hcheck : check P cap n = true := by
    rw [← checkC_eq n hcap']
    unfold checkC
    simpa using hchk
  obtain ⟨hfi, hidx⟩ := index_le_of_check hg hgen hcheck
  refine ⟨hfi, hidx, ?_⟩
  intro u hu
  have hinv := enumerate_inv hg cap
  have hst : (enumerateC P cap).toSt = enumerate P cap := enumerateC_toSt hcap'
  have hcode : u.map (colCode ws) ∈ colCodes ws us := List.mem_map_of_mem hu
  simp only [List.all_eq_true, beq_iff_eq] at hwalk
  have hw := hwalk _ hcode
  rw [walkRootC_eq] at hw
  have hw' : walkRoot P.L (enumerate P cap).tab (enumerate P cap).fwd (enumerate P cap).next 1
      (u.map (colCode ws)) = some 1 := by
    rw [← hst] at *
    simpa using hw
  have hlet : ∀ y ∈ u.map (colCode ws), y < P.L := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact colCode_lt ws x
  have hrel := walkRoot_spec hinv (enumerate P cap).next _ 1 1 hlet
    (by have := hinv.next_two; omega) hw'
  rw [rel_iff, Inv.rep_one hinv, one_mul, inv_one, mul_one, evalWord_colCode] at hrel
  exact hrel

end CFSG.CosetTable
