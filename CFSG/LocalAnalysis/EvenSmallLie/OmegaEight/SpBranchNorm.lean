module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchBits
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem xorBits_eq_of_lt {f : ℕ → ℕ} {c m : ℕ} (hc : c < 2 ^ m) :
    ∀ k, xorBits (m + k) f c = xorBits m f c := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, xorBits_succ, ih,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right Nat.two_pos (by omega)))]
    simp

theorem xorBits_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j, j < n → f j = g j) (c : ℕ) :
    xorBits n f c = xorBits n g c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih fun j hj => h j (by omega), h n (by omega)]

@[expose] def nStep (n q : ℕ) (M cb : ℕ → ℕ → ℕ) (olen : ℕ → ℕ) (i : ℕ)
    (st : List ℕ × List (List ℕ)) : List (List ℕ × List (List ℕ)) :=
  ((List.range (2 ^ n)).filter fun v => v != 0 && olen v == olen (2 ^ i)).filterMap fun v =>
    let Vs := st.1 ++ [v]
    let newc := (List.range q).map fun j =>
      (st.2.getD j []).filter fun e => M e v == xorBits (i + 1) (fun l => Vs.getD l 0) (cb j i)
    if newc.all (fun l => !l.isEmpty) then some (Vs, newc) else none

@[expose] def nStates (n q : ℕ) (M cb : ℕ → ℕ → ℕ) (olen : ℕ → ℕ) (m : ℕ) :
    List (List ℕ × List (List ℕ)) :=
  (List.range m).foldl (fun acc i => acc.flatMap (nStep n q M cb olen i))
    [([], List.replicate q (List.range (2 ^ q)))]

@[expose] def nSearch (n q : ℕ) (M cb : ℕ → ℕ → ℕ) (olen : ℕ → ℕ) : List (List ℕ) :=
  (nStates n q M cb olen n).map Prod.fst

theorem mem_nSearch {n q : ℕ} {M cb : ℕ → ℕ → ℕ} {olen : ℕ → ℕ} {V E : ℕ → ℕ}
    (hV : ∀ i, i < n → V i ≠ 0 ∧ V i < 2 ^ n ∧ olen (V i) = olen (2 ^ i))
    (hE : ∀ j, j < q → E j < 2 ^ q)
    (hM : ∀ i, i < n → ∀ j, j < q → M (E j) (V i) = xorBits (i + 1) V (cb j i)) :
    (List.range n).map V ∈ nSearch n q M cb olen := by
  have key : ∀ m, m ≤ n → ∃ cands : List (List ℕ), cands.length = q ∧
      (∀ j, j < q → E j ∈ cands.getD j []) ∧
      ((List.range m).map V, cands) ∈ nStates n q M cb olen m := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨List.replicate q (List.range (2 ^ q)), by simp, fun j hj => ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_replicate]
        exact List.mem_range.2 (hE j hj)
      · simp [nStates]
    | succ m ih =>
      intro hm
      obtain ⟨cands, hlen, hmem, hst⟩ := ih (by omega)
      have hVm := hV m (by omega)
      set newc := (List.range q).map fun j =>
        (cands.getD j []).filter fun e =>
          M e (V m) == xorBits (m + 1) (fun l => ((List.range m).map V ++ [V m]).getD l 0) (cb j m)
      have hgetD : ∀ l, l < m + 1 → ((List.range m).map V ++ [V m]).getD l 0 = V l := by
        intro l hl
        by_cases h : l < m
        · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
            List.getElem_map, List.getElem_range]
        · have hl' : l = m := by omega
          subst hl'
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
      have hnewc : ∀ j, j < q → E j ∈ newc.getD j [] := by
        intro j hj
        rw [List.getD_eq_getElem _ _ (by simpa [newc] using hj)]
        simp only [newc, List.getElem_map, List.getElem_range, List.mem_filter, beq_iff_eq]
        refine ⟨hmem j hj, ?_⟩
        rw [hM m (by omega) j hj]
        exact xorBits_congr (fun l hl => (hgetD l hl).symm) _
      refine ⟨newc, by simp [newc], hnewc, ?_⟩
      rw [nStates, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine List.mem_flatMap.2 ⟨_, hst, ?_⟩
      unfold nStep
      refine List.mem_filterMap.2 ⟨V m, List.mem_filter.2 ⟨List.mem_range.2 hVm.2.1, ?_⟩, ?_⟩
      · simp [hVm.1, hVm.2.2]
      · have hall : (newc.all fun l => !l.isEmpty) = true := by
          rw [List.all_eq_true]
          intro l hl
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hl
          have := hnewc j (List.mem_range.1 hj)
          rw [List.getD_eq_getElem _ _ (by simpa [newc] using List.mem_range.1 hj)] at this
          simp only [newc, List.getElem_map, List.getElem_range] at this
          simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]
          exact ⟨_, this⟩
        rw [ite_eq_left hall, List.map_append, List.map_singleton]
  obtain ⟨cands, -, -, hst⟩ := key n le_rfl
  exact List.mem_map.2 ⟨_, hst, rfl⟩

end CFSG.EvenSmallLie.OmegaEight.SpBranch
