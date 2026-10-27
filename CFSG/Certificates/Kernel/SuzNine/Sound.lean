module

public import Certificates.Data.Kernel.SuzNine.Orb
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.GetD

public section

namespace CFSG.KC.SuzNine

theorem testBit_fldK (k t i : ℕ) :
    (fldK k t).testBit i = (decide (i < 11) && k.testBit (11 * t + i)) := by
  change ((k >>> (11 * t)) &&& (2 ^ 11 - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem fldK_ext {a b : ℕ} (h : ∀ t, fldK a t = fldK b t) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e : j = 11 * (j / 11) + j % 11 := (Nat.div_add_mod j 11).symm
  have hj := congrArg (fun x => x.testBit (j % 11)) (h (j / 11))
  simp only [testBit_fldK, ← e, Nat.mod_lt j (Nat.succ_pos 10), decide_true,
    Bool.true_and] at hj
  exact hj

theorem fldK_lor (a b t : ℕ) : fldK (a ||| b) t = fldK a t ||| fldK b t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_fldK, testBit_fldK, testBit_fldK, Nat.testBit_or]
  cases decide (i < 11) <;> rfl

theorem fldK_eq_zero_iff_lt {v : ℕ} (hv : v < 2 ^ 11) (i : ℕ) (hi : 11 ≤ i) : v.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right Nat.two_pos hi))

theorem fldK_shiftLeft {v : ℕ} (hv : v < 2 ^ 11) (p t : ℕ) :
    fldK (v <<< (11 * p)) t = if p = t then v else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fldK, Nat.testBit_shiftLeft]
  split_ifs with hpt
  · subst hpt
    by_cases hi : i < 11
    · simp [hi]
    · simp [hi, fldK_eq_zero_iff_lt hv i (by omega)]
  · rw [Nat.zero_testBit]
    by_cases hi : i < 11
    · rcases Nat.lt_or_gt_of_ne hpt with h | h
      · have h1 : 11 * p + 11 ≤ 11 * t := by omega
        rw [fldK_eq_zero_iff_lt hv _ (by omega)]
        simp
      · have h1 : 11 * t + i < 11 * p := by omega
        simp [hi, show ¬ (11 * t + i ≥ 11 * p) by omega]
    · simp [hi]

@[expose] noncomputable def packP (n : ℕ) (v p : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc ||| (v i <<< (11 * p i))) n

theorem actK_eq (k g : ℕ) : actK k g = packP 30 (fun t => fldK g (fldK k t)) id := rfl

theorem setK_eq (c k g : ℕ) :
    setK c k g = packP c (fun i => fldK g (fldK k i)) (fun i => belowK c k g (fldK g (fldK k i))) :=
  rfl

theorem packP_succ (n : ℕ) (v p : ℕ → ℕ) :
    packP (n + 1) v p = packP n v p ||| (v n <<< (11 * p n)) := rfl

theorem fldK_packP {n : ℕ} {v p : ℕ → ℕ} (hv : ∀ i < n, v i < 2 ^ 11)
    (hp : ∀ i < n, ∀ j < n, p i = p j → i = j) :
    (∀ i < n, fldK (packP n v p) (p i) = v i) ∧
      ∀ t, (∀ i < n, p i ≠ t) → fldK (packP n v p) t = 0 := by
  induction n with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun t _ => ?_⟩
    change fldK 0 t = 0
    unfold fldK
    simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hv i (by omega))
      (fun i hi j hj => hp i (by omega) j (by omega))
    refine ⟨fun i hi => ?_, fun t ht => ?_⟩
    · rw [packP_succ, fldK_lor, fldK_shiftLeft (hv n (by omega))]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · rw [ih1 i hi', if_neg (fun e => by have := hp n (by omega) i hi e; omega), Nat.or_zero]
      · rw [if_pos rfl, ih2 _ (fun j hj e => by have := hp j (by omega) i (by omega) e; omega),
          Nat.zero_or]
    · rw [packP_succ, fldK_lor, fldK_shiftLeft (hv n (by omega)), if_neg (ht n (by omega)),
        ih2 t (fun i hi => ht i (by omega)), Nat.zero_or]

theorem fldK_shl_zero (k : ℕ) : fldK (k <<< 11) 0 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fldK, Nat.testBit_shiftLeft, Nat.zero_testBit]
  by_cases hi : i < 11 <;> simp [hi]

theorem fldK_shl_succ (k s : ℕ) : fldK (k <<< 11) (s + 1) = fldK k s := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fldK, testBit_fldK, Nat.testBit_shiftLeft,
    show 11 * (s + 1) + i - 11 = 11 * s + i by omega]
  have h : 11 ≤ 11 * (s + 1) + i := by omega
  simp [h]

theorem listKey_cons (a : ℕ) (L : List ℕ) : listKey (a :: L) = a + (listKey L <<< 11) := rfl

theorem fldK_listKey : ∀ (L : List ℕ), (∀ x ∈ L, x < 2 ^ 11) → ∀ t, fldK (listKey L) t = L.getD t 0
  | [], _, t => by
    change fldK 0 t = 0
    unfold fldK
    simp
  | a :: L, hL, t => by
    have ha : a < 2 ^ 11 := hL a List.mem_cons_self
    rw [listKey_cons, Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt ha, fldK_lor]
    have ha' : fldK a t = if 0 = t then a else 0 := by
      have := fldK_shiftLeft ha 0 t
      rwa [Nat.mul_zero, Nat.shiftLeft_zero] at this
    rw [ha']
    cases t with
    | zero => rw [fldK_shl_zero, if_pos rfl, Nat.zero_or]; rfl
    | succ s =>
      rw [fldK_shl_succ, if_neg (by omega), Nat.or_zero,
        fldK_listKey L (fun x hx => hL x (List.mem_cons_of_mem a hx)) s]
      rfl

theorem belowK_eq (c k g v : ℕ) :
    belowK c k g v = (List.range c).countP (fun j => decide (fldK g (fldK k j) < v)) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change Bool.rec (motive := fun _ => ℕ) (belowK c k g v) (belowK c k g v + 1)
      (Nat.blt (fldK g (fldK k c)) v) = _
    rw [List.range_succ, List.countP_append, ← ih]
    by_cases h : fldK g (fldK k c) < v
    · rw [show Nat.blt (fldK g (fldK k c)) v = true from Nat.blt_eq.mpr h]
      simp [h]
    · rw [show Nat.blt (fldK g (fldK k c)) v = false from by
        rw [Bool.eq_false_iff]; intro h'; exact h (Nat.blt_eq.mp h')]
      simp [h]

theorem getD_mem' {M : List ℕ} {r : ℕ} (hr : r < M.length) : M.getD r 0 ∈ M := by
  rw [List.getD_eq_getElem _ _ hr]
  exact List.getElem_mem hr

theorem countP_lt_getD : ∀ {M : List ℕ}, M.Pairwise (· < ·) → ∀ r < M.length,
    M.countP (fun x => decide (x < M.getD r 0)) = r
  | [], _, r, hr => absurd hr (by simp)
  | a :: M, hM, r, hr => by
    rw [List.pairwise_cons] at hM
    cases r with
    | zero =>
      rw [List.countP_cons, List.getD_cons_zero, List.countP_eq_zero.2 (fun x hx => by
        simpa using (hM.1 x hx).le)]
      simp
    | succ r =>
      have hr' : r < M.length := by simpa using hr
      have ha : a < M.getD r 0 := hM.1 _ (getD_mem' hr')
      simp only [List.countP_cons, List.getD_cons_succ, countP_lt_getD hM.2 r hr', ha,
        decide_true, if_true]

theorem setK_listKey {L M : List ℕ} {g : ℕ} {f : ℕ → ℕ} (hL : ∀ x ∈ L, x < 2 ^ 11)
    (hLd : L.Nodup) (hg : ∀ x ∈ L, fldK g x = f x)
    (hf : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) (hM : M.Pairwise (· < ·))
    (hMf : M.Perm (L.map f)) (hMb : ∀ x ∈ M, x < 2 ^ 11) :
    setK L.length (listKey L) g = listKey M := by
  have hfk : ∀ i, fldK (listKey L) i = L.getD i 0 := fldK_listKey L hL
  let v : ℕ → ℕ := fun i => fldK g (fldK (listKey L) i)
  have hvi : ∀ i < L.length, v i = f (L.getD i 0) := fun i hi => by
    change fldK g (fldK (listKey L) i) = _
    rw [hfk]
    exact hg _ (getD_mem' hi)
  have hlen : M.length = L.length := by rw [hMf.length_eq, List.length_map]
  have hmapv : L.map f = (List.range L.length).map v := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range,
      hvi i (by simpa using h1), List.getD_eq_getElem _ _ (by simpa using h1)]
  have hpos : ∀ i < L.length, ∃ r < L.length, M.getD r 0 = v i := by
    intro i hi
    have hm : v i ∈ M := by
      rw [hMf.mem_iff, hmapv]
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    obtain ⟨r, hr, e⟩ := List.getElem_of_mem hm
    exact ⟨r, hlen ▸ hr, by rw [List.getD_eq_getElem _ _ hr, e]⟩
  have hbelow : ∀ r < L.length, belowK L.length (listKey L) g (M.getD r 0) = r := by
    intro r hr
    rw [belowK_eq]
    refine Eq.trans ?_ (countP_lt_getD hM r (by omega))
    rw [hMf.countP_eq, hmapv, List.countP_map]
    rfl
  have hp : ∀ i < L.length, belowK L.length (listKey L) g (v i) < L.length ∧
      M.getD (belowK L.length (listKey L) g (v i)) 0 = v i := by
    intro i hi
    obtain ⟨r, hr, e⟩ := hpos i hi
    rw [← e, hbelow r hr]
    exact ⟨hr, rfl⟩
  have hvinj : ∀ i < L.length, ∀ j < L.length, v i = v j → i = j := by
    intro i hi j hj e
    rw [hvi i hi, hvi j hj] at e
    have := hf _ (getD_mem' hi) _ (getD_mem' hj) e
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at this
    exact (List.Nodup.getElem_inj_iff hLd).1 this
  have hpinj : ∀ i < L.length, ∀ j < L.length,
      belowK L.length (listKey L) g (v i) = belowK L.length (listKey L) g (v j) → i = j := by
    intro i hi j hj e
    apply hvinj i hi j hj
    rw [← (hp i hi).2, ← (hp j hj).2, e]
  have hvb : ∀ i < L.length, v i < 2 ^ 11 := fun i hi => by
    rw [← (hp i hi).2]
    exact hMb _ (getD_mem' (by rw [hlen]; exact (hp i hi).1))
  obtain ⟨hF1, hF2⟩ := fldK_packP hvb hpinj
  rw [setK_eq]
  apply fldK_ext
  intro t
  rw [fldK_listKey M hMb]
  by_cases ht : t < L.length
  · obtain ⟨i, hi, e⟩ : ∃ i < L.length, v i = M.getD t 0 := by
      have hm : M.getD t 0 ∈ (List.range L.length).map v := by
        rw [← hmapv, ← hMf.mem_iff]
        exact getD_mem' (by omega)
      obtain ⟨i, hi, e⟩ := List.mem_map.1 hm
      exact ⟨i, List.mem_range.1 hi, e⟩
    have hb : belowK L.length (listKey L) g (v i) = t := by rw [e]; exact hbelow t ht
    have h1 := hF1 i hi
    rw [hb] at h1
    exact h1.trans e
  · rw [hF2 t (fun i hi e => by have := (hp i hi).1; omega),
      List.getD_eq_default _ _ (by omega)]

@[expose] def ptList {n : ℕ} (s : Finset (Fin n)) : List ℕ := (s.sort (· ≤ ·)).map Fin.val

theorem ptList_pairwise {n : ℕ} (s : Finset (Fin n)) : (ptList s).Pairwise (· < ·) := by
  have h1 : (s.sort (· ≤ ·)).Pairwise (· < ·) :=
    ((s.pairwise_sort (· ≤ ·)).and (s.sort_nodup (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2
  exact h1.map _ (fun a b h => Fin.lt_iff_val_lt_val.1 h)

theorem ptList_nodup {n : ℕ} (s : Finset (Fin n)) : (ptList s).Nodup :=
  (ptList_pairwise s).imp (fun h => ne_of_lt h)

theorem mem_ptList {n : ℕ} (s : Finset (Fin n)) (x : ℕ) :
    x ∈ ptList s ↔ ∃ y ∈ s, (y : ℕ) = x := by
  simp [ptList]

theorem ptList_length {n : ℕ} (s : Finset (Fin n)) : (ptList s).length = s.card := by
  simp [ptList]

theorem setK_map {n : ℕ} (hn : n ≤ 2 ^ 11) (g : Equiv.Perm (Fin n)) {P : ℕ}
    (hP : ∀ x : Fin n, fldK P x = g x) (s : Finset (Fin n)) :
    setK s.card (listKey (ptList s)) P = listKey (ptList (s.map g.toEmbedding)) := by
  classical
  let f : ℕ → ℕ := fun x => if h : x < n then (g ⟨x, h⟩ : ℕ) else 0
  have hf' : ∀ y : Fin n, f y = g y := fun y => by simp [f, y.2]
  rw [← ptList_length s]
  refine setK_listKey (f := f) ?_ (ptList_nodup s) ?_ ?_ (ptList_pairwise _) ?_ ?_
  · intro x hx
    obtain ⟨y, -, rfl⟩ := (mem_ptList s x).1 hx
    exact lt_of_lt_of_le y.2 hn
  · intro x hx
    obtain ⟨y, -, rfl⟩ := (mem_ptList s x).1 hx
    rw [hP, hf']
  · intro x hx y hy e
    obtain ⟨x, -, rfl⟩ := (mem_ptList s x).1 hx
    obtain ⟨y, -, rfl⟩ := (mem_ptList s y).1 hy
    rw [hf', hf'] at e
    exact congrArg Fin.val (g.injective (Fin.ext e))
  · refine (List.perm_ext_iff_of_nodup (ptList_nodup _) ?_).2 fun x => ?_
    · refine List.Nodup.map_on (fun a ha b hb e => ?_) (ptList_nodup s)
      obtain ⟨a, -, rfl⟩ := (mem_ptList s a).1 ha
      obtain ⟨b, -, rfl⟩ := (mem_ptList s b).1 hb
      rw [hf', hf'] at e
      exact congrArg Fin.val (g.injective (Fin.ext e))
    · rw [mem_ptList, List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.1 hy
        exact ⟨z, (mem_ptList s _).2 ⟨z, hz, rfl⟩, by rw [hf']; rfl⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨z, hz, rfl⟩ := (mem_ptList s y).1 hy
        exact ⟨g z, Finset.mem_map_of_mem _ hz, by rw [hf']⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := (mem_ptList _ x).1 hx
    exact lt_of_lt_of_le y.2 hn

end CFSG.KC.SuzNine

end
