module

public import CFSG.Certificates.Kernel.RootOrbit.Sound
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighCheck

public section

namespace CFSG.KC.RootOrbit

open CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {n : ℕ}

theorem mem_foldIter_succ_of_mem (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) {k : ℕ}
    {l : List ℤ} (hl : l ∈ foldIter M a b k) : l ∈ foldIter M a b (k + 1) := by
  simp only [foldIter, List.mem_dedup, List.mem_append]
  exact Or.inl hl

theorem mem_foldIter_of_mem_foldMoves (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) {k : ℕ}
    {l m : List ℤ} (hl : l ∈ foldIter M a b k) (hm : m ∈ foldMoves M a b l) :
    m ∈ foldIter M a b (k + 1) := by
  simp only [foldIter, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨l, hl, hm⟩

theorem foldIter_mono (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) {k k' : ℕ} (hk : k ≤ k')
    {l : List ℤ} (hl : l ∈ foldIter M a b k) : l ∈ foldIter M a b k' := by
  induction k', hk using Nat.le_induction with
  | base => exact hl
  | succ k' _ ih => exact mem_foldIter_succ_of_mem M a b ih

theorem unit_mem_foldIter (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) (i : Fin n) :
    List.ofFn (Pi.single i 1 : Fin n → ℤ) ∈ foldIter M a b 0 := by
  simp only [foldIter, List.mem_dedup, List.mem_map, List.mem_finRange, true_and]
  exact ⟨i, rfl⟩

theorem length_reflL (rows : List (List ℤ)) (i : ℕ) (x : List ℤ) :
    (reflL rows i x).length = x.length := by
  simp [reflL]

theorem foldMv_mem_foldMoves (M : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) {c : ℕ}
    (hc : c = 0 ∨ (c - 1 < n ∧ c - 1 ≠ a ∧ c - 1 ≠ b)) {x : List ℤ} (hx : x.length = n) :
    foldMv (rowsOf M) a b c x ∈ foldMoves M a b x := by
  by_cases hc0 : c = 0
  · have hb' : (reflL (rowsOf M) b x).length = n := by rw [length_reflL, hx]
    simp only [foldMv, hc0, if_true]
    rw [reflL_eq M a hb', reflL_eq M b hx]
    exact List.mem_cons_self
  · obtain ⟨hn, ha, hb⟩ := hc.resolve_left hc0
    simp only [foldMv, hc0, if_false]
    rw [reflL_eq M ⟨c - 1, hn⟩ hx]
    refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨⟨c - 1, hn⟩, ?_, rfl⟩)
    simp only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨fun e => ha (congrArg Fin.val e), fun e => hb (congrArg Fin.val e)⟩

theorem mem_foldIter_of_foldCertB {M : Matrix (Fin n) (Fin n) ℤ} {rows : List (List ℤ)}
    {a b : Fin n} {R : List (List ℤ)} {F : List (ℕ × ℕ × ℕ)} (hrows : rowsOf M = rows)
    (h : foldCertB rows n a b R F = true) (hlen : ∀ x ∈ R, x.length = n) {x : List ℤ}
    (hx : x ∈ R) : x ∈ foldIter M a b 30 := by
  subst hrows
  simp only [foldCertB, List.all_eq_true, List.mem_range] at h
  have hdepth : ∀ d k, k < R.length → (F.getD k (0, 0, 0)).1 = d →
      R.getD k [] ∈ foldIter M a b d := by
    intro d
    induction d with
    | zero =>
      intro k hk hd
      have := h k hk
      simp only [foldAt, hd, Bool.and_eq_true, decide_eq_true_eq, if_true, beq_iff_eq] at this
      obtain ⟨-, hi, he⟩ := this
      rw [he, unitL_eq ⟨_, hi⟩]
      exact unit_mem_foldIter M a b _
    | succ d ih =>
      intro k hk hd
      have := h k hk
      simp only [foldAt, hd, Bool.and_eq_true, decide_eq_true_eq, Nat.add_one_ne_zero, if_false,
        beq_iff_eq, Nat.add_right_cancel_iff, Bool.or_eq_true, bne_iff_ne, ne_eq] at this
      obtain ⟨-, ⟨⟨hpd, hp⟩, hm⟩, he⟩ := this
      have hpl : (R.getD (F.getD k (0, 0, 0)).2.1 []).length = n := by
        rw [List.getD_eq_getElem _ _ hp]
        exact hlen _ (List.getElem_mem hp)
      rw [he]
      refine mem_foldIter_of_mem_foldMoves M a b (ih _ hp hpd) (foldMv_mem_foldMoves M a b ?_ hpl)
      rcases hm with hm | ⟨⟨hm1, hm2⟩, hm3⟩
      · exact Or.inl hm
      · exact Or.inr ⟨hm1, hm2, hm3⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have h30 := h k hk
  simp only [foldAt, Bool.and_eq_true, decide_eq_true_eq] at h30
  rw [← List.getD_eq_getElem _ [] hk]
  exact foldIter_mono M a b h30.1 (hdepth _ k hk rfl)

theorem all_eq_of_mem_iff {α : Type*} {L L' : List α} (h : ∀ l, l ∈ L ↔ l ∈ L')
    (f : α → Bool) : L.all f = L'.all f := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun H l hl => H l ((h l).2 hl), fun H l hl => H l ((h l).1 hl)⟩

theorem dGraphOK_of_certs {M : Matrix (Fin n) (Fin n) ℤ} {rows : List (List ℤ)} {a b : Fin n}
    {P : List (List ℕ)} {W F : List (ℕ × ℕ × ℕ)} {N : ℕ} (hrows : rowsOf M = rows)
    (hr : rootCertB rows n P W N = true) (hf : foldCertB rows n a b (signedL P) F = true)
    (ho : orthOK M a b (signedL P) = true)
    (hs : (sepPairB M (2 * n) a b && M a b == 0 && adjOK M a b) = true) :
    dGraphOK M a b N = true := by
  obtain ⟨-, -, hlen, -, hmem⟩ := rootCertB_spec hrows hr
  have h1 := orbitOK_of_rootCertB hrows hr
  simp only [orbitOK, Bool.and_eq_true] at h1
  have ho' : orthOK M a b (orbitIter M 30) = true := by
    rw [orthOK, all_eq_of_mem_iff hmem]
    exact ho
  have hr' : reachOK M a b (orbitIter M 30) 30 = true := by
    rw [reachOK, all_eq_of_mem_iff hmem, List.all_eq_true]
    exact fun x hx => decide_eq_true (mem_foldIter_of_foldCertB hrows hf hlen hx)
  simp only [Bool.and_eq_true] at hs
  simp only [dGraphOK, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h1.1, h1.2⟩, hs.1.1⟩, hs.1.2⟩, ho'⟩, hr'⟩, hs.2⟩

end CFSG.KC.RootOrbit
