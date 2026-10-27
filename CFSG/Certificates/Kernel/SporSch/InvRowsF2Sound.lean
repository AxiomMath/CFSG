module

public import CFSG.Certificates.Kernel.SporSch.PairJ3InvSound

public section

namespace CFSG.KS.SporSch.InvF2

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.KS.SporSch.PF2

private def bt (u j : ℕ) : ZMod 2 := if u.testBit j then 1 else 0

private theorem bt_xor (u w j : ℕ) : bt (u ^^^ w) j = bt u j + bt w j := by
  unfold bt
  rw [Nat.testBit_xor]
  cases u.testBit j <;> cases w.testBit j <;> decide

private theorem testBit_eq_of_bt {u w j : ℕ} (h : bt u j = bt w j) :
    u.testBit j = w.testBit j := by
  unfold bt at h
  cases hu : u.testBit j <;> cases hw : w.testBit j <;> simp only [hu, hw] at h <;>
    first | rfl | exact absurd h (by decide)

private theorem bt_shiftLeft (i j : ℕ) : bt (1 <<< i) j = if i = j then 1 else 0 := by
  unfold bt
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j <;> simp [h]

private theorem add_self_two (y : ZMod 2) : y + y = 0 := by
  fin_cases y <;> decide

private theorem bt_fold (R : Array ℕ) (v k n : ℕ) :
    bt ((List.range n).foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) 0)
        k = ∑ j ∈ Finset.range n, bt v j * bt (R[j]?.getD 0) k := by
  induction n with
  | zero => simp [bt]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← ih]
    by_cases hv : v.testBit n
    · have : bt v n = 1 := by simp [bt, hv]
      simp only [hv, if_true]
      rw [bt_xor, this, one_mul]
    · have : bt v n = 0 := by simp [bt, hv]
      simp only [hv, if_false, Bool.false_eq_true]
      rw [this, zero_mul, add_zero]

private theorem bt_vecMulN (d : ℕ) (R : Array ℕ) (v k : ℕ) :
    bt (vecMulN d R v) k = ∑ j ∈ Finset.range d, bt v j * bt (R[j]?.getD 0) k :=
  bt_fold R v k d

private theorem vecMulN_xor (d : ℕ) (R : Array ℕ) (u w : ℕ) :
    vecMulN d R (u ^^^ w) = vecMulN d R u ^^^ vecMulN d R w := by
  apply Nat.eq_of_testBit_eq
  intro k
  apply testBit_eq_of_bt
  rw [bt_xor, bt_vecMulN, bt_vecMulN, bt_vecMulN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bt_xor, add_mul]

private theorem vecMulN_shiftLeft (d : ℕ) (R : Array ℕ) {i : ℕ} (hi : i < d) :
    vecMulN d R (1 <<< i) = R[i]?.getD 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  apply testBit_eq_of_bt
  rw [bt_vecMulN]
  simp only [bt_shiftLeft, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [hi]

private theorem vecMulN_lt (d : ℕ) (R : Array ℕ) (hR : ∀ j < d, R[j]?.getD 0 < 2 ^ d) (v : ℕ) :
    vecMulN d R v < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  have h0 : bt (vecMulN d R v) k = bt 0 k := by
    rw [bt_vecMulN]
    have : bt 0 k = 0 := by simp [bt]
    rw [this]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : R[j]?.getD 0 < 2 ^ k :=
      lt_of_lt_of_le (hR j (Finset.mem_range.mp hj)) (Nat.pow_le_pow_right (by norm_num) hk)
    simp [bt, Nat.testBit_eq_false_of_lt hj']
  simpa using testBit_eq_of_bt h0

private def dot (d u : ℕ) (x : ℕ → ZMod 2) : ZMod 2 := ∑ j ∈ Finset.range d, bt u j * x j

private theorem dot_xor (d u w : ℕ) (x : ℕ → ZMod 2) : dot d (u ^^^ w) x = dot d u x + dot d w x := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bt_xor, add_mul]

private theorem dot_vecMulN (d : ℕ) (R : Array ℕ) (v : ℕ) (x : ℕ → ZMod 2) :
    dot d (vecMulN d R v) x = ∑ j ∈ Finset.range d, bt v j * dot d (R[j]?.getD 0) x := by
  unfold dot
  simp_rw [bt_vecMulN, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem dot_shiftLeft (d : ℕ) {i : ℕ} (hi : i < d) (x : ℕ → ZMod 2) :
    dot d (1 <<< i) x = x i := by
  unfold dot
  simp only [bt_shiftLeft, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [hi]

private theorem get_bang (a : Array ℕ) (i : ℕ) : a[i]! = a[i]?.getD 0 := by
  rw [getElem!_def]
  cases a[i]? <;> rfl

private theorem get_set (a : Array ℕ) {i : ℕ} (hi : i < a.size) (v k : ℕ) :
    (a.set! i v)[k]! = if i = k then v else a[k]! := by
  rw [get_bang, get_bang, Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : i = k
  · subst h; simp [hi]
  · simp [h]

private theorem size_set (a : Array ℕ) (i v : ℕ) : (a.set! i v).size = a.size := by
  simp [Array.set!]

private theorem get_mulRows (d : ℕ) (X Y : Array ℕ) {i : ℕ} (hi : i < X.size) :
    (mulRows d X Y)[i]! = vecMulN d Y X[i]! := by
  rw [get_bang, get_bang, mulRows, Array.getElem?_map]
  simp [hi]

private theorem get_idRows {d i : ℕ} (hi : i < d) : (idRows d)[i]! = 1 <<< i := by
  rw [get_bang, idRows, Array.getElem?_ofFn]
  simp [hi]

private theorem size_idRows (d : ℕ) : (idRows d).size = d := by
  simp [idRows]

private theorem arr_ext {d : ℕ} {a b : Array ℕ} (ha : a.size = d) (hb : b.size = d)
    (h : ∀ i < d, a[i]! = b[i]!) : a = b := by
  refine Array.ext (by omega) fun i h1 h2 => ?_
  have := h i (by omega)
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

private theorem piv_fold (d c : ℕ) (a : Array ℕ) (l : List ℕ) (hl : ∀ i ∈ l, c ≤ i ∧ i < d)
    (piv : ℕ) (hp : piv ≠ d → c ≤ piv ∧ piv < d ∧ a[piv]!.testBit c = true) :
    (l.foldl (fun piv i => if (piv == d && a[i]!.testBit c) = true then i else piv) piv ≠ d →
      c ≤ l.foldl (fun piv i => if (piv == d && a[i]!.testBit c) = true then i else piv) piv ∧
      l.foldl (fun piv i => if (piv == d && a[i]!.testBit c) = true then i else piv) piv < d ∧
      a[l.foldl (fun piv i => if (piv == d && a[i]!.testBit c) = true then i else piv)
        piv]!.testBit c = true) ∧
    (l.foldl (fun piv i => if (piv == d && a[i]!.testBit c) = true then i else piv) piv = d →
      piv = d ∧ ∀ i ∈ l, a[i]!.testBit c = false) := by
  induction l generalizing piv with
  | nil => exact ⟨hp, fun h => ⟨h, by simp⟩⟩
  | cons x l ih =>
    simp only [List.foldl_cons]
    have hx := hl x (by simp)
    have hp' : (if (piv == d && a[x]!.testBit c) = true then x else piv) ≠ d →
        c ≤ (if (piv == d && a[x]!.testBit c) = true then x else piv) ∧
        (if (piv == d && a[x]!.testBit c) = true then x else piv) < d ∧
        a[(if (piv == d && a[x]!.testBit c) = true then x else piv)]!.testBit c = true := by
      by_cases hc : (piv == d && a[x]!.testBit c) = true
      · simp only [hc, if_true]
        simp only [Bool.and_eq_true] at hc
        exact fun _ => ⟨hx.1, hx.2, hc.2⟩
      · simp only [hc, if_false, Bool.false_eq_true]
        exact hp
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hl i (by simp [hi])) _ hp'
    refine ⟨ih1, fun hr => ?_⟩
    obtain ⟨e, hrest⟩ := ih2 hr
    by_cases hc : (piv == d && a[x]!.testBit c) = true
    · simp only [hc, if_true] at e
      omega
    · simp only [hc, if_false, Bool.false_eq_true] at e
      refine ⟨e, ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · simp only [e, beq_self_eq_true, Bool.true_and] at hc
        simpa using hc
      · exact hrest i hi

private theorem pivA_spec (d c : ℕ) (a : Array ℕ) :
    (pivA d c a < d → c ≤ pivA d c a ∧ a[pivA d c a]!.testBit c = true) ∧
    (¬ pivA d c a < d → ∀ i, c ≤ i → i < d → a[i]!.testBit c = false) := by
  obtain ⟨h1, h2⟩ := piv_fold d c a (List.range' c (d - c))
    (fun i hi => by rw [List.mem_range'_1] at hi; omega) d (fun h => absurd rfl h)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a1, -, a3⟩ := h1 (by unfold pivA at h; omega)
    exact ⟨a1, a3⟩
  · have hd : pivA d c a = d := by
      by_contra hne
      exact h (h1 hne).2.1
    intro i hci hid
    exact (h2 hd).2 i (by rw [List.mem_range'_1]; omega)

variable {d : ℕ} {M : Array ℕ}

private structure Inv (d : ℕ) (M : Array ℕ) (c : ℕ) (s : Array ℕ × Array ℕ) : Prop where
  sz1 : s.1.size = d
  sz2 : s.2.size = d
  lin : ∀ i < d, vecMulN d M s.2[i]! = s.1[i]!
  ker : ∀ x : ℕ → ZMod 2, (∀ i < d, dot d s.1[i]! x = 0) → ∀ i < d, dot d (M[i]?.getD 0) x = 0
  col : ∀ i < d, ∀ j < c, s.1[i]!.testBit j = decide (i = j)

private structure EInv (d : ℕ) (M : Array ℕ) (c ap rp : ℕ) (s : Array ℕ × Array ℕ) : Prop where
  sz1 : s.1.size = d
  sz2 : s.2.size = d
  pa : s.1[c]! = ap
  pr : s.2[c]! = rp
  lin : ∀ i < d, vecMulN d M s.2[i]! = s.1[i]!
  ker : ∀ x : ℕ → ZMod 2, (∀ i < d, dot d s.1[i]! x = 0) → ∀ i < d, dot d (M[i]?.getD 0) x = 0
  col : ∀ i < d, ∀ j < c, s.1[i]!.testBit j = decide (i = j)

private theorem inv_init (hM : M.size = d) : Inv d M 0 (M, idRows d) where
  sz1 := hM
  sz2 := size_idRows d
  lin i hi := by
    rw [get_idRows hi, vecMulN_shiftLeft d M hi, get_bang]
  ker x h i hi := by simpa [get_bang] using h i hi
  col i _ j hj := absurd hj (Nat.not_lt_zero j)

private theorem piv_exists {L : Array ℕ} (hL : mulRows d L M = idRows d) {c : ℕ} (hc : c < d)
    {s : Array ℕ × Array ℕ} (h : Inv d M c s)
    (hno : ∀ i, c ≤ i → i < d → s.1[i]!.testBit c = false) : False := by
  have hLs : L.size = d := by
    have := congrArg Array.size hL
    rwa [mulRows, Array.size_map, size_idRows] at this
  let x : ℕ → ZMod 2 := fun j => if j = c then 1 else if j < c then bt s.1[j]! c else 0
  have hx : ∀ i < d, dot d s.1[i]! x = 0 := by
    intro i hi
    unfold dot
    have hcm : c ∈ Finset.range d := Finset.mem_range.mpr hc
    by_cases hic : i < c
    · have him : i ∈ Finset.range d := Finset.mem_range.mpr hi
      rw [Finset.sum_eq_add_of_mem c i hcm him (by omega)]
      · have e1 : x c = 1 := by simp [x]
        have e2 : x i = bt s.1[i]! c := by simp [x, hic, show i ≠ c by omega]
        have e3 : bt s.1[i]! i = 1 := by simp [bt, h.col i hi i hic]
        rw [e1, e2, e3, mul_one, one_mul, add_self_two]
      · intro j hj hne
        have hjd := Finset.mem_range.mp hj
        by_cases hjc : j < c
        · have : bt s.1[i]! j = 0 := by
            simp [bt, h.col i hi j hjc, show i ≠ j by omega]
          rw [this, zero_mul]
        · have : x j = 0 := by simp [x, hjc, hne.1]
          rw [this, mul_zero]
    · rw [Finset.sum_eq_single c]
      · have : bt s.1[i]! c = 0 := by simp [bt, hno i (by omega) hi]
        rw [this, zero_mul]
      · intro j hj hne
        have hjd := Finset.mem_range.mp hj
        by_cases hjc : j < c
        · have : bt s.1[i]! j = 0 := by
            simp [bt, h.col i hi j hjc, show i ≠ j by omega]
          rw [this, zero_mul]
        · have : x j = 0 := by simp [x, hjc, hne]
          rw [this, mul_zero]
      · intro hn
        exact absurd hcm hn
  have hMx := h.ker x hx
  have key : x c = 0 := by
    rw [← dot_shiftLeft d hc x, ← get_idRows hc, ← hL, get_mulRows d L M (by omega),
      dot_vecMulN]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hMx j (Finset.mem_range.mp hj), mul_zero]
  have : x c = 1 := by simp [x]
  rw [this] at key
  exact absurd key (by decide)

private theorem einv_swap {c : ℕ} (hc : c < d) {s : Array ℕ × Array ℕ} (h : Inv d M c s) {p : ℕ}
    (hcp : c ≤ p) (hpd : p < d) :
    EInv d M c s.1[p]! s.2[p]!
      ((s.1.set! p s.1[c]!).set! c s.1[p]!, (s.2.set! p s.2[c]!).set! c s.2[p]!) := by
  have g1 : ∀ k, ((s.1.set! p s.1[c]!).set! c s.1[p]!)[k]! =
      if c = k then s.1[p]! else if p = k then s.1[c]! else s.1[k]! := by
    intro k
    rw [get_set _ (by rw [size_set]; have := h.sz1; omega), get_set _ (by have := h.sz1; omega)]
  have g2 : ∀ k, ((s.2.set! p s.2[c]!).set! c s.2[p]!)[k]! =
      if c = k then s.2[p]! else if p = k then s.2[c]! else s.2[k]! := by
    intro k
    rw [get_set _ (by rw [size_set]; have := h.sz2; omega), get_set _ (by have := h.sz2; omega)]
  refine ⟨by simp [size_set, h.sz1], by simp [size_set, h.sz2], by rw [g1]; simp,
    by rw [g2]; simp, ?_, ?_, ?_⟩
  · intro i hi
    simp only [g1, g2]
    split_ifs
    · exact h.lin p hpd
    · exact h.lin c hc
    · exact h.lin i hi
  · intro x hx i hi
    refine h.ker x (fun k hk => ?_) i hi
    have hpre : ∃ k' < d, ((s.1.set! p s.1[c]!).set! c s.1[p]!)[k']! = s.1[k]! := by
      by_cases hkc : k = c
      · subst hkc
        refine ⟨p, hpd, ?_⟩
        rw [g1]
        by_cases hcp : k = p
        · subst hcp; simp
        · simp [hcp]
      · by_cases hkp : k = p
        · exact ⟨c, hc, by rw [g1]; simp [hkp]⟩
        · exact ⟨k, hk, by rw [g1]; simp [Ne.symm hkc, Ne.symm hkp]⟩
    obtain ⟨k', hk', e⟩ := hpre
    rw [← e]
    exact hx k' hk'
  · intro i hi j hj
    simp only [g1]
    split_ifs with h1 h2
    · rw [h.col p hpd j hj]; simp; omega
    · rw [h.col c hc j hj]; simp; omega
    · exact h.col i hi j hj

private theorem einv_step {c ap rp : ℕ} (hc : c < d) (hap : ap.testBit c = true)
    {s : Array ℕ × Array ℕ} (h : EInv d M c ap rp s) {i : ℕ} (hi : i < d) :
    EInv d M c ap rp (elimStepA c ap rp s i) ∧
      (∀ k : ℕ, s.1[k]!.testBit c = false → (elimStepA c ap rp s i).1[k]!.testBit c = false) ∧
      (i ≠ c → (elimStepA c ap rp s i).1[i]!.testBit c = false) := by
  unfold elimStepA
  by_cases hb : (i != c && s.1[i]!.testBit c) = true
  · simp only [hb, if_true]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    obtain ⟨hic, hbit⟩ := hb
    have g1 : ∀ k, (s.1.set! i (s.1[i]! ^^^ ap))[k]! = if i = k then s.1[i]! ^^^ ap else s.1[k]! :=
      fun k => get_set _ (by rw [h.sz1]; exact hi) _ k
    have g2 : ∀ k, (s.2.set! i (s.2[i]! ^^^ rp))[k]! = if i = k then s.2[i]! ^^^ rp else s.2[k]! :=
      fun k => get_set _ (by rw [h.sz2]; exact hi) _ k
    have hapc : ∀ j < c, ap.testBit j = false := by
      intro j hj
      rw [← h.pa, h.col c hc j hj]
      simp; omega
    refine ⟨⟨by simp [size_set, h.sz1], by simp [size_set, h.sz2], ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [g1, if_neg hic, h.pa]
    · rw [g2, if_neg hic, h.pr]
    · intro k hk
      rw [g1, g2]
      split_ifs
      · rw [vecMulN_xor, h.lin i hi, ← h.pr, h.lin c hc, h.pa]
      · exact h.lin k hk
    · intro x hx k hk
      refine h.ker x (fun m hm => ?_) k hk
      by_cases hm' : i = m
      · subst hm'
        have e := hx i hi
        have ec := hx c hc
        rw [g1, if_pos rfl, dot_xor] at e
        rw [g1, if_neg hic, h.pa] at ec
        rw [ec, add_zero] at e
        exact e
      · have := hx m hm
        rw [g1, if_neg hm'] at this
        exact this
    · intro k hk j hj
      rw [g1]
      split_ifs with hik
      · rw [Nat.testBit_xor, h.col i hi j hj, hapc j hj, hik]
        simp
      · exact h.col k hk j hj
    · intro k hk
      rw [g1]
      split_ifs with hik
      · subst hik; rw [hbit] at hk; exact absurd hk (by decide)
      · exact hk
    · intro _
      rw [g1, if_pos rfl, Nat.testBit_xor, hbit, hap]
      rfl
  · simp only [hb, if_false, Bool.false_eq_true]
    refine ⟨h, fun k hk => hk, fun hic => ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and] at hb
    simpa using hb hic

private theorem einv_fold {c ap rp : ℕ} (hc : c < d) (hap : ap.testBit c = true) :
    ∀ (l : List ℕ) (s : Array ℕ × Array ℕ), (∀ i ∈ l, i < d) → EInv d M c ap rp s →
      EInv d M c ap rp (l.foldl (elimStepA c ap rp) s) ∧
      ∀ k : ℕ, (k ∈ l ∨ s.1[k]!.testBit c = false) → k ≠ c →
        (l.foldl (elimStepA c ap rp) s).1[k]!.testBit c = false := by
  intro l
  induction l with
  | nil => exact fun s _ h => ⟨h, fun k hk _ => by simpa using hk⟩
  | cons i l ih =>
    intro s hl h
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := einv_step hc hap h (hl i (by simp))
    obtain ⟨i1, i2⟩ := ih _ (fun j hj => hl j (by simp [hj])) h1
    refine ⟨i1, fun k hk hkc => ?_⟩
    rcases hk with hk | hk
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact i2 k (Or.inr (h3 hkc)) hkc
      · exact i2 k (Or.inl hk) hkc
    · exact i2 k (Or.inr (h2 k hk)) hkc

private theorem inv_col {L : Array ℕ} (hL : mulRows d L M = idRows d) {c : ℕ} (hc : c < d)
    {s : Array ℕ × Array ℕ} (h : Inv d M c s) : Inv d M (c + 1) (colA d c s) := by
  obtain ⟨hp1, hp2⟩ := pivA_spec d c s.1
  by_cases hp : pivA d c s.1 < d
  · obtain ⟨hcp, hbit⟩ := hp1 hp
    unfold colA
    rw [if_pos hp]
    have e0 := einv_swap hc h hcp hp
    obtain ⟨e, hz⟩ := einv_fold hc hbit (List.range' 0 d) _
      (fun i hi => by rw [List.mem_range'_1] at hi; omega) e0
    unfold elimA
    refine ⟨e.sz1, e.sz2, e.lin, e.ker, fun i hi j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact e.col i hi j hj
    · by_cases hij : i = j
      · subst hij
        rw [e.pa, hbit]
        simp
      · rw [hz i (Or.inl (by rw [List.mem_range'_1]; omega)) hij]
        simp [hij]
  · exact (piv_exists hL hc h (hp2 hp)).elim

private theorem inv_fold {L : Array ℕ} (hL : mulRows d L M = idRows d) :
    ∀ (k c : ℕ) (s : Array ℕ × Array ℕ), c + k ≤ d → Inv d M c s →
      Inv d M (c + k) ((List.range' c k).foldl (fun s c => colA d c s) s) := by
  intro k
  induction k with
  | zero => exact fun c s _ h => h
  | succ k ih =>
    intro c s hk h
    rw [List.range'_succ, List.foldl_cons]
    have := ih (c + 1) _ (by omega) (inv_col hL (by omega) h)
    rwa [show c + 1 + k = c + (k + 1) by omega] at this

theorem invRowsF2_mul_of_mul {d : ℕ} {M L : Array ℕ} (hM : M.size = d)
    (hMr : ∀ i < d, M[i]?.getD 0 < 2 ^ d) (hL : mulRows d L M = idRows d) :
    mulRows d (invRowsF2 d M) M = idRows d := by
  have H := inv_fold hL d 0 (M, idRows d) (by omega) (inv_init hM)
  rw [Nat.zero_add] at H
  rw [invRowsF2_fold]
  set s := (List.range' 0 d).foldl (fun s c => colA d c s) (M, idRows d)
  refine arr_ext (by rw [mulRows, Array.size_map, H.sz2]) (size_idRows d) fun i hi => ?_
  rw [get_mulRows d _ M (by rw [H.sz2]; exact hi), get_idRows hi, H.lin i hi]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases hj : j < d
  · rw [H.col i hi j hj]
  · have hlt : s.1[i]! < 2 ^ j := by
      rw [← H.lin i hi]
      exact lt_of_lt_of_le (vecMulN_lt d M hMr _) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hlt]
    simp
    omega

end CFSG.KS.SporSch.InvF2
