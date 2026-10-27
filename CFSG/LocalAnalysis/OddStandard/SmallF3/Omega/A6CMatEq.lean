module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CMatLin
public import Mathlib.Data.Nat.Digits.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.A6C

private lemma a6c_foldl_base3 (l : List ℕ) (init : ℕ) :
    l.foldl (fun k e => k * 3 + e) init =
      init * 3 ^ l.length + Nat.ofDigits 3 l.reverse := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
      rw [List.foldl_cons, ih (init * 3 + a), List.reverse_cons, Nat.ofDigits_append,
        Nat.ofDigits_singleton]
      simp only [List.length_cons, List.length_reverse, pow_succ]
      ring

private lemma a6c_packM_eq_ofDigits (x : Mat) :
    packM x = Nat.ofDigits 3 x.toList.reverse := by
  rw [packM, ← Array.foldl_toList]
  simpa using a6c_foldl_base3 x.toList 0

private lemma a6c_packM_injective (n : ℕ) {x y : Mat} (hx : A6CWf n x) (hy : A6CWf n y)
    (h : packM x = packM y) : x = y := by
  rw [A6CWf.eq_def] at hx hy
  have hlen : x.toList.length = y.toList.length := by
    rw [← Array.size_eq_length_toList, ← Array.size_eq_length_toList, hx.1, hy.1]
  have hwx : ∀ e ∈ x.toList, e < 3 := fun e he => hx.2 e (Array.mem_toList_iff.mp he)
  have hwy : ∀ e ∈ y.toList, e < 3 := fun e he => hy.2 e (Array.mem_toList_iff.mp he)
  have hdig : Nat.ofDigits 3 x.toList.reverse = Nat.ofDigits 3 y.toList.reverse := by
    rw [← a6c_packM_eq_ofDigits x, ← a6c_packM_eq_ofDigits y, h]
  have hrev : x.toList.reverse = y.toList.reverse :=
    Nat.ofDigits_inj_of_len_eq (by norm_num) (by simpa using hlen)
      (by simpa [List.mem_reverse] using hwx)
      (by simpa [List.mem_reverse] using hwy) hdig
  have hlist : x.toList = y.toList := by
    simpa using congrArg List.reverse hrev
  exact Array.toList_inj.mp hlist

private lemma a6c_neg3_neg3 (e : ℕ) (he : e < 3) : 2 * (2 * e % 3) % 3 = e := by
  have h3 : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases h3 with rfl | rfl | rfl <;> rfl

private lemma a6c_negM_negM (n : ℕ) {x : Mat} (hx : A6CWf n x) : negM (negM x) = x := by
  rw [A6CWf.eq_def] at hx
  apply Array.toList_inj.mp
  simp only [negM, Array.toList_map, List.map_map]
  trans x.toList.map id
  · apply List.map_congr_left
    intro e he
    simpa only [Function.comp_apply, id] using
      a6c_neg3_neg3 e (hx.2 e (Array.mem_toList_iff.mp he))
  · exact List.map_id x.toList

private lemma a6c_keyM_negM (n : ℕ) {y : Mat} (hy : A6CWf n y) :
    keyM (negM y) = keyM y := by
  simp only [keyM]
  rw [a6c_negM_negM n hy, Nat.min_comm]

theorem a6c_eqP_iff (n : ℕ) {x y : Mat} (hx : A6CWf n x) (hy : A6CWf n y) :
    eqP x y = true ↔
      A6CToMat n x = A6CToMat n y ∨ A6CToMat n x = -A6CToMat n y := by
  simp only [eqP, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, a6c_toMat_negM])
  · rintro (h | h)
    · exact Or.inl (a6c_toMat_injective n hx hy h)
    · refine Or.inr (a6c_toMat_injective n hx (a6c_wf_negM n hy) ?_)
      rw [a6c_toMat_negM]
      exact h

theorem a6c_simOK_iff (n : ℕ) (g : Mat) :
    simOK n g = true ↔ A6CWf n g ∧ A6CSimMat (A6CToMat n g) := by
  constructor
  · intro h
    rw [simOK, Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨⟨hsize, hall⟩, hmul⟩ := h
    have hsize' : g.size = n * n := by simpa [beq_iff_eq] using hsize
    have hall' : ∀ e ∈ g, e < 3 := by
      intro e he
      exact decide_eq_true_eq.mp (Array.all_eq_true'.mp hall e he)
    have hwf : A6CWf n g := by
      rw [A6CWf.eq_def]
      exact ⟨hsize', hall'⟩
    refine ⟨hwf, ?_⟩
    rw [A6CSimMat.eq_def]
    rcases hmul with hmul | hmul
    · rw [beq_iff_eq] at hmul
      exact Or.inl (by
        have h := congrArg (A6CToMat n) hmul
        simpa [a6c_toMat_mulN, a6c_toMat_trN, a6c_toMat_idN] using h)
    · rw [beq_iff_eq] at hmul
      exact Or.inr (by
        have h := congrArg (A6CToMat n) hmul
        simpa [a6c_toMat_mulN, a6c_toMat_trN, a6c_toMat_negM, a6c_toMat_idN] using h)
  · rintro ⟨hwf, hsim | hsim⟩
    · rw [A6CWf.eq_def] at hwf
      rw [simOK, Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
      · simpa [beq_iff_eq] using hwf.1
      · exact Array.all_eq_true'.mpr (fun e he => decide_eq_true_eq.mpr (hwf.2 e he))
      · rw [beq_iff_eq]
        refine a6c_toMat_injective n (a6c_wf_mulN n g (trN n g)) (a6c_wf_idN n) ?_
        rw [a6c_toMat_mulN, a6c_toMat_trN, a6c_toMat_idN]
        exact hsim
    · rw [A6CWf.eq_def] at hwf
      rw [simOK, Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨⟨?_, ?_⟩, Or.inr ?_⟩
      · simpa [beq_iff_eq] using hwf.1
      · exact Array.all_eq_true'.mpr (fun e he => decide_eq_true_eq.mpr (hwf.2 e he))
      · rw [beq_iff_eq]
        refine a6c_toMat_injective n (a6c_wf_mulN n g (trN n g))
          (a6c_wf_negM n (a6c_wf_idN n)) ?_
        rw [a6c_toMat_mulN, a6c_toMat_trN, a6c_toMat_negM, a6c_toMat_idN]
        exact hsim

theorem a6c_commP_iff (n : ℕ) (x y : Mat) :
    commP n x y = true ↔
      A6CToMat n x * A6CToMat n y = A6CToMat n y * A6CToMat n x ∨
        A6CToMat n x * A6CToMat n y = -(A6CToMat n y * A6CToMat n x) := by
  rw [commP, a6c_eqP_iff n (a6c_wf_mulN n x y) (a6c_wf_mulN n y x)]
  simp only [a6c_toMat_mulN]

theorem a6c_relP_iff (n : ℕ) (a x : Mat) :
    relP n a x = true ↔
      (A6CToMat n a * A6CToMat n a = 1 ∨ A6CToMat n a * A6CToMat n a = -1) ∧
      ((A6CToMat n a * A6CToMat n x) ^ 4 = 1 ∨ (A6CToMat n a * A6CToMat n x) ^ 4 = -1) ∧
      ((A6CToMat n x * A6CToMat n a * A6CToMat n x) ^ 5 = 1 ∨
        (A6CToMat n x * A6CToMat n a * A6CToMat n x) ^ 5 = -1) := by
  simp only [relP, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h1' := (a6c_eqP_iff n (a6c_wf_mulN n a a) (a6c_wf_idN n)).mp h1
    have h2' := (a6c_eqP_iff n (a6c_wf_powM n (mulN n a x) 4) (a6c_wf_idN n)).mp h2
    have h3' := (a6c_eqP_iff n (a6c_wf_powM n (mulN n (mulN n x a) x) 5)
      (a6c_wf_idN n)).mp h3
    refine ⟨?_, ?_, ?_⟩
    · rcases h1' with h | h
      · exact Or.inl (by simpa [a6c_toMat_mulN, a6c_toMat_idN] using h)
      · exact Or.inr (by simpa [a6c_toMat_mulN, a6c_toMat_idN] using h)
    · rcases h2' with h | h
      · exact Or.inl (by simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)
      · exact Or.inr (by simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)
    · rcases h3' with h | h
      · exact Or.inl (by
          simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)
      · exact Or.inr (by
          simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [a6c_eqP_iff n (a6c_wf_mulN n a a) (a6c_wf_idN n)]
      rcases h1 with h | h
      · exact Or.inl (by simpa [a6c_toMat_mulN, a6c_toMat_idN] using h)
      · exact Or.inr (by simpa [a6c_toMat_mulN, a6c_toMat_idN] using h)
    · rw [a6c_eqP_iff n (a6c_wf_powM n (mulN n a x) 4) (a6c_wf_idN n)]
      rcases h2 with h | h
      · exact Or.inl (by simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)
      · exact Or.inr (by simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)
    · rw [a6c_eqP_iff n (a6c_wf_powM n (mulN n (mulN n x a) x) 5) (a6c_wf_idN n)]
      rcases h3 with h | h
      · exact Or.inl (by simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)
      · exact Or.inr (by simpa [a6c_toMat_powM, a6c_toMat_mulN, a6c_toMat_idN] using h)

theorem a6c_keyM_eq_iff (n : ℕ) {x y : Mat} (hx : A6CWf n x) (hy : A6CWf n y) :
    keyM x = keyM y ↔ A6CToMat n x = A6CToMat n y ∨ A6CToMat n x = -A6CToMat n y := by
  have hxneg : A6CWf n (negM x) := a6c_wf_negM n hx
  have hyneg : A6CWf n (negM y) := a6c_wf_negM n hy
  constructor
  · intro hkey
    have hmin : min (packM x) (packM (negM x)) = min (packM y) (packM (negM y)) := by
      simpa only [keyM] using hkey
    have hcases : packM x = packM y ∨ packM x = packM (negM y) ∨
        packM (negM x) = packM y ∨ packM (negM x) = packM (negM y) := by
      by_cases ha : packM x ≤ packM (negM x)
      · by_cases hb : packM y ≤ packM (negM y)
        · left
          calc packM x = min (packM x) (packM (negM x)) := (Nat.min_eq_left ha).symm
            _ = min (packM y) (packM (negM y)) := hmin
            _ = packM y := Nat.min_eq_left hb
        · right; left
          calc packM x = min (packM x) (packM (negM x)) := (Nat.min_eq_left ha).symm
            _ = min (packM y) (packM (negM y)) := hmin
            _ = packM (negM y) := Nat.min_eq_right (Nat.le_of_not_le hb)
      · by_cases hb : packM y ≤ packM (negM y)
        · right; right; left
          calc packM (negM x) = min (packM x) (packM (negM x)) :=
                (Nat.min_eq_right (Nat.le_of_not_le ha)).symm
            _ = min (packM y) (packM (negM y)) := hmin
            _ = packM y := Nat.min_eq_left hb
        · right; right; right
          calc packM (negM x) = min (packM x) (packM (negM x)) :=
                (Nat.min_eq_right (Nat.le_of_not_le ha)).symm
            _ = min (packM y) (packM (negM y)) := hmin
            _ = packM (negM y) := Nat.min_eq_right (Nat.le_of_not_le hb)
    rcases hcases with hxy | hxy | hxy | hxy
    · left
      rw [a6c_packM_injective n hx hy hxy]
    · right
      have hxny : x = negM y := a6c_packM_injective n hx hyneg hxy
      rw [hxny, a6c_toMat_negM]
    · right
      have hnx : negM x = y := a6c_packM_injective n hxneg hy hxy
      have hxny : x = negM y := by
        have h := congrArg negM hnx
        simpa [a6c_negM_negM n hx] using h
      rw [hxny, a6c_toMat_negM]
    · left
      have hnx : negM x = negM y := a6c_packM_injective n hxneg hyneg hxy
      have hxeq : x = y := by
        have h := congrArg negM hnx
        simpa [a6c_negM_negM n hx, a6c_negM_negM n hy] using h
      rw [hxeq]
  · rintro (hxy | hxy)
    · rw [a6c_toMat_injective n hx hy hxy]
    · have hmat : A6CToMat n x = A6CToMat n (negM y) := by
        rw [a6c_toMat_negM]
        exact hxy
      have hxny : x = negM y := a6c_toMat_injective n hx hyneg hmat
      rw [hxny, a6c_keyM_negM n hy]

private lemma a6c_sortedLT_of_zip_tail {s : List ℕ}
    (h : (s.zip s.tail).all (fun p => decide (p.1 < p.2)) = true) : s.SortedLT := by
  rw [List.sortedLT_iff_isChain, List.isChain_iff_getElem]
  intro i hi
  have hlt : i < (s.zip s.tail).length := by
    rw [List.length_zip, List.length_tail]
    omega
  have hmem : (s[i], s[i + 1]) ∈ s.zip s.tail := by
    have hget : (s.zip s.tail)[i] = (s[i], s[i + 1]) := by
      rw [List.getElem_zip]
      simp [List.getElem_tail]
    have hmem' := List.getElem_mem hlt
    simpa [hget] using hmem'
  have hp := (List.all_eq_true.mp h) (s[i], s[i + 1]) hmem
  simpa using hp

theorem a6c_nodupKeys_sound {ks : List ℕ} (h : nodupKeys ks = true) : ks.Nodup := by
  have hsort : (ks.mergeSort (fun a b => decide (a ≤ b))).SortedLT := by
    apply a6c_sortedLT_of_zip_tail
    simpa only [nodupKeys] using h
  exact List.nodup_mergeSort.mp hsort.nodup

theorem a6c_keysNodup_sound {L : Array Mat} (h : keysNodup L = true) {i j : ℕ}
    (hi : i < L.size) (hj : j < L.size) (hij : i ≠ j) : keyM L[i]! ≠ keyM L[j]! := by
  intro hEq
  have hnd : (L.toList.map keyM).Nodup := by
    apply a6c_nodupKeys_sound
    simpa only [keysNodup] using h
  have hi' : i < (L.toList.map keyM).length := by simpa using hi
  have hj' : j < (L.toList.map keyM).length := by simpa using hj
  have hgeti : L[i]! = L.toList[i] := by
    rw [getElem!_pos L i hi]
    simpa using (Array.getElem_toList (xs := L) (i := i) (by simpa using hi)).symm
  have hgetj : L[j]! = L.toList[j] := by
    rw [getElem!_pos L j hj]
    simpa using (Array.getElem_toList (xs := L) (i := j) (by simpa using hj)).symm
  have hmap : (L.toList.map keyM)[i] = (L.toList.map keyM)[j] := by
    rw [List.getElem_map, List.getElem_map, ← hgeti, ← hgetj]
    exact hEq
  exact hij (hnd.getElem_inj_iff.mp hmap)

end CFSG.OddStandard.SmallF3.Omega
