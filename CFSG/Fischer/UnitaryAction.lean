module

public import CFSG.Fischer.Unitary
public import CFSG.Fischer.UnitaryCode
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open CFSG.F4.Native Matrix

theorem codeOf_vecOfCode {c : ℕ} (hc : c < 4096) : codeOf (vecOfCode c) = c := by
  show c / 4 ^ 0 % 4 + 4 * (c / 4 ^ 1 % 4) + 16 * (c / 4 ^ 2 % 4) + 64 * (c / 4 ^ 3 % 4) +
    256 * (c / 4 ^ 4 % 4) + 1024 * (c / 4 ^ 5 % 4) = c
  norm_num
  omega

theorem lead_smul {c : F4} (hc : c ≠ 0) (w : Fin 6 → F4) : lead (c • w) = c * lead w := by
  unfold lead
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or]
  split_ifs <;> simp_all

private theorem cube_eq_one : ∀ c : F4, c ≠ 0 → c * c * c = 1 := by decide

theorem normV_smul {c : F4} (hc : c ≠ 0) (w : Fin 6 → F4) : normV (c • w) = normV w := by
  unfold normV
  rw [lead_smul hc, smul_smul]
  congr 1
  calc c * lead w * (c * lead w) * c = (c * c * c) * (lead w * lead w) := by ring
    _ = lead w * lead w := by rw [cube_eq_one c hc, one_mul]

theorem lead_ne_zero {w : Fin 6 → F4} (hw : w ≠ 0) : lead w ≠ 0 := by
  unfold lead
  split_ifs with h0 h1 h2 h3 h4
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · intro h5
    apply hw
    funext i
    fin_cases i <;> simp_all

theorem normV_eq_smul {w : Fin 6 → F4} (hw : w ≠ 0) : ∃ c : F4, c ≠ 0 ∧ normV w = c • w :=
  ⟨lead w * lead w, mul_ne_zero (lead_ne_zero hw) (lead_ne_zero hw), rfl⟩

theorem codeOf_injective : Function.Injective codeOf := by
  intro v w h
  rw [← vecOfCode_codeOf v, ← vecOfCode_codeOf w, h]

theorem codeOf_eq_zero_iff (w : Fin 6 → F4) : codeOf w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h0 : codeOf (0 : Fin 6 → F4) = 0 := by decide
    exact codeOf_injective (h.trans h0.symm)
  · rintro rfl; decide

theorem mem_uPts {c : ℕ} : c ∈ uPts ↔ c < 4096 ∧ c ≠ 0 ∧ hermC c c = 0 ∧ normC c = c := by
  unfold uPts
  rw [List.mem_toArray, List.mem_filter, List.mem_range]
  simp [bne_iff_ne]
  tauto

structure PtsFacts : Prop where
  size : uPts.size = 693
  sorted : ∀ i < 692, uPts[i]! < uPts[i + 1]!
  complete : ∀ c < 4096, c ≠ 0 → hermC c c = 0 → normC c ∈ uPts

theorem ptsFacts_of (h : uPtsOK = true) : PtsFacts := by
  unfold uPtsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, Array.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, -⟩ := h
  refine ⟨h1, h3, fun c hc hc0 hh => ?_⟩
  rcases h4 c hc with (h | h) | h
  · exact absurd h hc0
  · exact absurd hh h
  · exact h

section Pts

variable (hP : PtsFacts)
include hP

theorem uPts_get_mem {i : ℕ} (hi : i < 693) : uPts[i]! ∈ uPts := by
  rw [getElem!_pos uPts i (by rw [hP.size]; exact hi)]
  exact Array.getElem_mem _

theorem uPts_strictMono {i j : ℕ} (hij : i < j) (hj : j < 693) : uPts[i]! < uPts[j]! := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact lt_trans (ih h (by omega)) (hP.sorted j (by omega))
    · exact hP.sorted i (by omega)

theorem uPts_inj {i j : ℕ} (hi : i < 693) (hj : j < 693) (h : uPts[i]! = uPts[j]!) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd h (ne_of_lt (uPts_strictMono hP hij hj))
  · exact hij
  · exact absurd h (ne_of_gt (uPts_strictMono hP hij hi))

end Pts

@[expose] def uVec (i : ℕ) : W := vecOfCode uPts[i]!

@[expose] def ptIdx (w : W) : ℕ := uPts.toList.idxOf (normC (codeOf w))

section Act

variable (hP : PtsFacts)
include hP

theorem uPts_nodup : uPts.toList.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj
  have hj' : j < 693 := by simpa [hP.size] using hj
  have hi' : i < 693 := by omega
  rw [List.getElem?_eq_getElem (by simpa using lt_trans hij hj),
    List.getElem?_eq_getElem hj]
  simp only [ne_eq, Option.some.injEq, Array.getElem_toList]
  intro h
  have := uPts_inj hP hi' hj' (by rw [getElem!_pos uPts i (by rw [hP.size]; exact hi'),
    getElem!_pos uPts j (by rw [hP.size]; exact hj')]; exact h)
  omega

theorem codeOf_uVec {i : ℕ} (hi : i < 693) : codeOf (uVec i) = uPts[i]! :=
  codeOf_vecOfCode (mem_uPts.1 (uPts_get_mem hP hi)).1

theorem uVec_ne_zero {i : ℕ} (hi : i < 693) : uVec i ≠ 0 := by
  intro h
  have := (mem_uPts.1 (uPts_get_mem hP hi)).2.1
  rw [← codeOf_uVec hP hi, h] at this
  exact this (by decide)

theorem uVec_iso {i : ℕ} (hi : i < 693) : hermStd (uVec i) (uVec i) = 0 := by
  have := (mem_uPts.1 (uPts_get_mem hP hi)).2.2.1
  rw [← codeOf_uVec hP hi, hermC_codeOf] at this
  exact (code_eq_zero_iff _).1 this

theorem normC_mem {w : W} (hw : w ≠ 0) (hiso : hermStd w w = 0) : normC (codeOf w) ∈ uPts :=
  hP.complete (codeOf w) (codeOf_lt w) (fun h0 => hw ((codeOf_eq_zero_iff w).1 h0))
    (by rw [hermC_codeOf, hiso]; rfl)

theorem ptIdx_lt {w : W} (hw : w ≠ 0) (hiso : hermStd w w = 0) : ptIdx w < 693 := by
  unfold ptIdx
  rw [← hP.size, ← Array.length_toList, List.idxOf_lt_length_iff]
  exact Array.mem_toList_iff.2 (normC_mem hP hw hiso)

theorem uPts_ptIdx {w : W} (hw : w ≠ 0) (hiso : hermStd w w = 0) :
    uPts[ptIdx w]! = normC (codeOf w) := by
  have hlt := ptIdx_lt hP hw hiso
  rw [getElem!_pos uPts _ (by rw [hP.size]; exact hlt), ← Array.getElem_toList]
  exact List.getElem_idxOf _

theorem uVec_ptIdx {w : W} (hw : w ≠ 0) (hiso : hermStd w w = 0) : uVec (ptIdx w) = normV w := by
  unfold uVec
  rw [uPts_ptIdx hP hw hiso, normC_codeOf, vecOfCode_codeOf]

theorem ptIdx_uVec {i : ℕ} (hi : i < 693) : ptIdx (uVec i) = i := by
  unfold ptIdx
  rw [codeOf_uVec hP hi, (mem_uPts.1 (uPts_get_mem hP hi)).2.2.2,
    getElem!_pos uPts i (by rw [hP.size]; exact hi), ← Array.getElem_toList]
  have := List.get_idxOf (uPts_nodup hP) ⟨i, by rw [Array.length_toList, hP.size]; exact hi⟩
  exact this

omit hP in
theorem ptIdx_smul {c : F4} (hc : c ≠ 0) (w : W) : ptIdx (c • w) = ptIdx w := by
  unfold ptIdx
  rw [normC_codeOf, normC_codeOf, normV_smul hc]

end Act

end CFSG.Fischer
