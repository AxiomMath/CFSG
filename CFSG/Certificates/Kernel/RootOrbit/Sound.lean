module

public import Certificates.Data.Kernel.RootOrbit.Check
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit

public section

namespace CFSG.KC.RootOrbit

open CFSG.HardMathSupport.Timmesfeld.RootAut

variable {n : ℕ}

theorem sum_zipWith_ofFn (f : Fin n → ℤ) (x : List ℤ) (hx : x.length = n) :
    (List.zipWith (· * ·) (List.ofFn f) x).sum = ∑ j, f j * x.getD j 0 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain _ | ⟨a, x⟩ := x
    · simp at hx
    · simp only [List.length_cons, Nat.add_right_cancel_iff] at hx
      rw [List.ofFn_succ, List.zipWith_cons_cons, List.sum_cons, ih _ x hx, Fin.sum_univ_succ]
      simp

theorem getD_rowsOf (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (rowsOf M).getD i [] = List.ofFn (M i) := by
  rw [rowsOf, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange,
    List.ofFn_eq_map]
  rfl

theorem reflL_eq (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) {x : List ℤ} (hx : x.length = n) :
    reflL (rowsOf M) i x = reflectList M i x := by
  have hc : dotL ((rowsOf M).getD i []) x = ∑ j, M i j * ofList (n := n) x j := by
    rw [getD_rowsOf, dotL, sum_zipWith_ofFn _ _ hx]
    rfl
  apply List.ext_getElem
  · simp [reflL, reflectList, hx]
  · intro j h1 h2
    have hn : j < n := by simpa [reflectList] using h2
    have hjx : j < x.length := hx ▸ hn
    simp only [reflL, List.getElem_modify, reflectList, List.getElem_ofFn, coordReflect,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hc]
    have hj : ofList (n := n) x ⟨j, hn⟩ = x[j] := by
      simp only [ofList, List.getD_eq_getElem _ _ hjx]
    rw [hj]
    by_cases h : (i : ℕ) = j
    · have : (⟨j, hn⟩ : Fin n) = i := Fin.ext h.symm
      simp [h, this]
    · have : (⟨j, hn⟩ : Fin n) ≠ i := fun e => h (congrArg Fin.val e).symm
      simp [h, this]

theorem length_reflectList (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (x : List ℤ) :
    (reflectList M i x).length = n := by
  simp [reflectList]

theorem ofList_negL (x : List ℤ) : ofList (n := n) (negL x) = -ofList (n := n) x := by
  funext j
  simp only [ofList, negL, Pi.neg_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases x[(j : ℕ)]? <;> simp

theorem reflectList_negL (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (x : List ℤ) :
    reflectList M i (negL x) = negL (reflectList M i x) := by
  rw [reflectList, reflectList, ofList_negL, negL, List.map_ofFn]
  congr 1
  funext j
  simp only [coordReflect, Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, mul_neg, Finset.sum_neg_distrib]
  ring

theorem negL_negL (x : List ℤ) : negL (negL x) = x := by
  simp [negL]

theorem unitL_eq (i : Fin n) : unitL n i = List.ofFn (Pi.single i 1 : Fin n → ℤ) := by
  apply List.ext_getElem
  · simp [unitL]
  · intro j h1 h2
    simp only [unitL, List.getElem_map, List.getElem_range, List.getElem_ofFn, Pi.single_apply]
    by_cases h : j = (i : ℕ)
    · simp [h]
    · have : (⟨j, by simpa using h2⟩ : Fin n) ≠ i := fun e => h (congrArg Fin.val e)
      simp [h, this]

theorem mem_orbitIter_succ_of_mem (M : Matrix (Fin n) (Fin n) ℤ) {k : ℕ} {l : List ℤ}
    (hl : l ∈ orbitIter M k) : l ∈ orbitIter M (k + 1) := by
  simp only [orbitIter, orbitStep, List.mem_dedup, List.mem_append]
  exact Or.inl hl

theorem reflectList_mem_orbitIter (M : Matrix (Fin n) (Fin n) ℤ) {k : ℕ} {l : List ℤ}
    (hl : l ∈ orbitIter M k) (i : Fin n) : reflectList M i l ∈ orbitIter M (k + 1) := by
  simp only [orbitIter, orbitStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_finRange, true_and]
  exact Or.inr ⟨l, hl, i, rfl⟩

theorem orbitIter_mono (M : Matrix (Fin n) (Fin n) ℤ) {k k' : ℕ} (hk : k ≤ k') {l : List ℤ}
    (hl : l ∈ orbitIter M k) : l ∈ orbitIter M k' := by
  induction k', hk using Nat.le_induction with
  | base => exact hl
  | succ k' _ ih => exact mem_orbitIter_succ_of_mem M ih

theorem unit_mem_orbitIter (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (i : Fin n) :
    List.ofFn (Pi.single i 1 : Fin n → ℤ) ∈ orbitIter M k := by
  refine orbitIter_mono M (Nat.zero_le k) ?_
  simp only [orbitIter, List.mem_dedup, List.mem_map, List.mem_finRange, true_and]
  exact ⟨i, rfl⟩

theorem orbitIter_subset {M : Matrix (Fin n) (Fin n) ℤ} {R : List (List ℤ)}
    (hu : ∀ i : Fin n, List.ofFn (Pi.single i 1 : Fin n → ℤ) ∈ R)
    (hc : ∀ l ∈ R, ∀ i : Fin n, reflectList M i l ∈ R) (k : ℕ) {l : List ℤ}
    (hl : l ∈ orbitIter M k) : l ∈ R := by
  induction k generalizing l with
  | zero =>
    simp only [orbitIter, List.mem_dedup, List.mem_map, List.mem_finRange, true_and] at hl
    obtain ⟨i, rfl⟩ := hl
    exact hu i
  | succ k ih =>
    simp only [orbitIter, orbitStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and] at hl
    rcases hl with hl | ⟨l', hl', i, rfl⟩
    · exact ih hl
    · exact hc _ (ih hl') i

theorem orbitOK_of_mem_iff {M : Matrix (Fin n) (Fin n) ℤ} {R : List (List ℤ)} {k : ℕ}
    (hR : R.Nodup) (hc : ∀ l ∈ R, ∀ i : Fin n, reflectList M i l ∈ R)
    (h : ∀ l, l ∈ orbitIter M k ↔ l ∈ R) : orbitOK M R.length k = true := by
  simp only [orbitOK, closedB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨fun i => unit_mem_orbitIter M k i, fun l hl i => (h _).2 (hc l ((h l).1 hl) i)⟩, ?_⟩
  exact ((List.perm_ext_iff_of_nodup (nodup_orbitIter M k) hR).2 h).length_eq

theorem mem_signedL_negL {P : List (List ℕ)} {x : List ℤ} (hx : x ∈ signedL P) :
    negL x ∈ signedL P := by
  simp only [signedL, List.mem_append, List.mem_map] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩ | ⟨z, ⟨y, hy, rfl⟩, rfl⟩
  · exact Or.inr ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  · exact Or.inl ⟨y, hy, (negL_negL _).symm⟩

theorem mem_of_memL {y : List ℤ} {R : List (List ℤ)} (h : memL y R = true) : y ∈ R := by
  simp only [memL, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨z, hz, -, rfl⟩ := h
  exact hz

theorem sum_negL (x : List ℤ) : (negL x).sum = -x.sum := by
  induction x with
  | nil => simp [negL]
  | cons a x ih =>
    simp only [negL, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem nodup_signedL {P : List (List ℕ)} (hnd : (P.map (List.map Int.ofNat)).Nodup)
    (hpos : ∀ x ∈ P.map (List.map Int.ofNat), 0 < x.sum) : (signedL P).Nodup := by
  rw [signedL, List.nodup_append]
  refine ⟨hnd, hnd.map (fun x y h => by rw [← negL_negL x, h, negL_negL]), ?_⟩
  intro x hx y hy hxy
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  have h1 := hpos x hx
  have h2 := hpos z hz
  rw [hxy, sum_negL] at h1
  omega

theorem rootCertB_spec {M : Matrix (Fin n) (Fin n) ℤ} {rows : List (List ℤ)}
    {P : List (List ℕ)} {W : List (ℕ × ℕ × ℕ)} {N : ℕ} (hrows : rowsOf M = rows)
    (h : rootCertB rows n P W N = true) :
    (signedL P).length = N ∧ (signedL P).Nodup ∧ (∀ x ∈ signedL P, x.length = n) ∧
      (∀ l ∈ signedL P, ∀ i : Fin n, reflectList M i l ∈ signedL P) ∧
      ∀ l, l ∈ orbitIter M 30 ↔ l ∈ signedL P := by
  subst hrows
  simp only [rootCertB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hN, hlen⟩, hnd⟩, hpos⟩, hu⟩, hcl⟩, hw⟩ := h
  have hnd := nodup_signedL hnd hpos
  set R := signedL P
  have hu' : ∀ i : Fin n, List.ofFn (Pi.single i 1 : Fin n → ℤ) ∈ R := fun i => by
    rw [← unitL_eq]
    exact mem_of_memL (hu i i.2)
  have hc : ∀ l ∈ R, ∀ i : Fin n, reflectList M i l ∈ R := by
    intro l hl i
    have hpos : ∀ y ∈ P.map (List.map Int.ofNat), reflectList M i y ∈ R := fun y hy => by
      rw [← reflL_eq M i (hlen y (List.mem_append_left _ hy))]
      exact mem_of_memL (hcl y hy i i.2)
    rcases List.mem_append.1 hl with hl | hl
    · exact hpos l hl
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
      rw [reflectList_negL]
      exact mem_signedL_negL (hpos y hy)
  have hdepth : ∀ d k, k < R.length → (W.getD k (0, 0, 0)).1 = d →
      R.getD k [] ∈ orbitIter M d := by
    intro d
    induction d with
    | zero =>
      intro k hk hd
      have := hw k hk
      simp only [witAt, hd, Bool.and_eq_true, decide_eq_true_eq, if_true, beq_iff_eq] at this
      obtain ⟨⟨hi, -⟩, he⟩ := this
      rw [he, unitL_eq ⟨_, hi⟩]
      exact unit_mem_orbitIter M 0 _
    | succ d ih =>
      intro k hk hd
      have := hw k hk
      simp only [witAt, hd, Bool.and_eq_true, decide_eq_true_eq, Nat.add_one_ne_zero, if_false,
        beq_iff_eq, Nat.add_right_cancel_iff] at this
      obtain ⟨⟨hi, -⟩, ⟨hpd, hp⟩, he⟩ := this
      rw [he, reflL_eq M ⟨_, hi⟩ (hlen _ (List.getD_eq_getElem _ _ hp ▸ List.getElem_mem hp))]
      exact reflectList_mem_orbitIter M (ih _ hp hpd) _
  have hsub : ∀ l ∈ R, l ∈ orbitIter M 30 := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    have h30 := hw k hk
    simp only [witAt, Bool.and_eq_true, decide_eq_true_eq] at h30
    rw [← List.getD_eq_getElem _ [] hk]
    exact orbitIter_mono M h30.1.2 (hdepth _ k hk rfl)
  exact ⟨hN, hnd, hlen, hc, fun l => ⟨orbitIter_subset hu' hc 30, hsub l⟩⟩

theorem orbitOK_of_rootCertB {M : Matrix (Fin n) (Fin n) ℤ} {rows : List (List ℤ)}
    {P : List (List ℕ)} {W : List (ℕ × ℕ × ℕ)} {N : ℕ} (hrows : rowsOf M = rows)
    (h : rootCertB rows n P W N = true) : orbitOK M N 30 = true := by
  obtain ⟨hN, hnd, -, hc, hmem⟩ := rootCertB_spec hrows h
  rw [← hN]
  exact orbitOK_of_mem_iff hnd hc hmem

end CFSG.KC.RootOrbit
