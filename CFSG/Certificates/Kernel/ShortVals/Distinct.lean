module

public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
import CFSG.Certificates.Kernel.Common.QSort

public section

namespace CFSG.KC.ShortVals

open CFSG.YGroups.Y443Native CFSG.KC.QSort

theorem invTable_fold (perm : Array Nat) (n : Nat) (hs : perm.size = n)
    (hlt : ∀ i (hi : i < perm.size), perm[i] < n)
    (hnd : ∀ i j (hi : i < perm.size) (hj : j < perm.size), perm[i] = perm[j] → i = j) :
    ∀ m, m ≤ n →
      ((List.range m).foldl (fun (acc : Array Nat) i => acc.setIfInBounds perm[i]! i)
          (Array.replicate n 0)).size = n ∧
      ∀ i, i < m → ((List.range m).foldl (fun (acc : Array Nat) i => acc.setIfInBounds perm[i]! i)
          (Array.replicate n 0))[perm[i]!]! = i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Array.size_setIfInBounds]
    refine ⟨ih1, fun i hi => ?_⟩
    have hm' : m < perm.size := by omega
    rw [getElem!_pos perm m hm']
    have hpm : perm[m] < n := hlt m hm'
    by_cases e : i = m
    · subst e
      rw [getElem!_pos perm i hm', getElem!_pos _ _ (by rw [Array.size_setIfInBounds, ih1]; exact hpm),
        Array.getElem_setIfInBounds_self]
    · have hi' : i < perm.size := by omega
      rw [getElem!_pos perm i hi',
        getElem!_pos _ _ (by rw [Array.size_setIfInBounds, ih1]; exact hlt i hi'),
        Array.getElem_setIfInBounds_ne (by rw [ih1]; exact hlt i hi')
          (fun h => e (hnd i m hi' hm' h.symm))]
      have := ih2 i (by omega)
      rwa [getElem!_pos perm i hi', getElem!_pos _ _ (by rw [ih1]; exact hlt i hi')] at this

theorem distinctCheck_of_injective (vals : Array Int)
    (h : ∀ p q, p < vals.size → q < vals.size → vals[p]! = vals[q]! → p = q) :
    distinctCheck vals = true := by
  let lt : Nat → Nat → Bool := fun a b => decide (vals[a]! < vals[b]!)
  have hperm : sortPerm vals = (Array.range vals.size).qsort lt := rfl
  have htrans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true := by
    intro a b c h1 h2
    simp only [lt, decide_eq_true_eq] at h1 h2 ⊢
    exact Int.lt_trans h1 h2
  have hasymm : ∀ a b, lt a b = true → lt b a = false := by
    intro a b h1
    simp only [lt, decide_eq_true_eq, decide_eq_false_iff_not] at h1 ⊢
    exact Int.not_lt.2 (Int.le_of_lt h1)
  have hsize : (sortPerm vals).size = vals.size := by
    rw [hperm, qsort_size, Array.size_range]
  have hP : (sortPerm vals).toList.Perm (List.range vals.size) := by
    have := qsort_perm (Array.range vals.size) lt
    rw [← hperm, Array.perm_iff_toList_perm, Array.toList_range] at this
    exact this
  have hnd : (sortPerm vals).toList.Nodup := hP.nodup_iff.2 List.nodup_range
  have hmem : ∀ x, x ∈ (sortPerm vals).toList ↔ x < vals.size := by
    intro x
    rw [hP.mem_iff, List.mem_range]
  have hlt : ∀ i (hi : i < (sortPerm vals).size), (sortPerm vals)[i] < vals.size := by
    intro i hi
    exact (hmem _).1 (Array.getElem_mem_toList hi)
  have hinj : ∀ i j (hi : i < (sortPerm vals).size) (hj : j < (sortPerm vals).size),
      (sortPerm vals)[i] = (sortPerm vals)[j] → i = j := by
    intro i j hi hj e
    have := List.Nodup.eq_of_getElem_eq hnd (i := i) (j := j) (by simpa using hi)
      (by simpa using hj)
    simp only [Array.getElem_toList] at this
    exact this e
  obtain ⟨hinvs, hinv⟩ := invTable_fold (sortPerm vals) vals.size hsize hlt hinj vals.size
    (Nat.le_refl _)
  unfold distinctCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq]
  refine ⟨fun p hp => ?_, fun i hi => ?_⟩
  · obtain ⟨j, hj, e⟩ := List.getElem_of_mem ((hmem p).2 hp)
    simp only [Array.getElem_toList, Array.length_toList] at e hj
    have hinvj := hinv j (by omega)
    rw [getElem!_pos _ j hj, e] at hinvj
    have hT : invTable (sortPerm vals) = (List.range vals.size).foldl
        (fun (acc : Array Nat) i => acc.setIfInBounds (sortPerm vals)[i]! i)
        (Array.replicate vals.size 0) := by
      unfold invTable
      rw [hsize]
      rfl
    rw [hT, hinvj, getElem!_pos _ j hj, e]
    exact ⟨by omega, rfl⟩
  · have hi1 : i + 1 < (sortPerm vals).size := by omega
    have hi0 : i < (sortPerm vals).size := by omega
    have hs := qsort_sorted (Array.range vals.size) lt htrans hasymm i (i + 1) (by omega)
      (by rw [← hperm]; exact hi1)
    simp only [← hperm] at hs
    rw [getElem!_pos _ i hi0, getElem!_pos _ (i + 1) hi1]
    simp only [lt, decide_eq_false_iff_not, Int.not_lt] at hs
    rcases Int.lt_or_eq_of_le hs with hs | hs
    · exact hs
    · have := h _ _ (hlt i hi0) (hlt (i + 1) hi1) hs
      have := hinj i (i + 1) hi0 hi1 this
      omega

end CFSG.KC.ShortVals
