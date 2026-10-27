module

public import CFSG.Certificates.Kernel.J4FamBits

public section

namespace CFSG.KC.J4Fam

open CFSG.Sporadic.J4.QT (compT actT idT)
open CFSG.EvenSporadicStandard.J4Std.DataLocal (maskOf testBit_maskOf foldl_maskOf_testBit)

theorem nodupL_spec : ∀ {l : List (List Nat)}, nodupL l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupL, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    exact List.nodup_cons.2 ⟨fun ha => h.1 a ha rfl, nodupL_spec h.2⟩

theorem invsOK_spec {INV : List (List Nat)} (h : invsOK INV = true) :
    INV.length = 191 ∧ idT ∉ INV ∧ INV.Nodup ∧ ∀ j < 191, WT (INV.getD j []) := by
  simp only [invsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun hm => h2 _ hm rfl, nodupL_spec h3, fun j hj => ?_⟩
  have hj' : j < INV.length := by omega
  rw [List.getD_eq_getElem _ _ hj']
  obtain ⟨hl, hx⟩ := h4 _ (List.getElem_mem hj')
  exact ⟨hl, fun x hx' => by have := hx x hx'; omega⟩

theorem getD_take {α : Type} (l : List α) {n r : Nat} (hr : r < n) (d : α) :
    (l.take n).getD r d = l.getD r d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hr, if_true]

theorem getD_drop {α : Type} (l : List α) (n r : Nat) (d : α) :
    (l.drop n).getD r d = l.getD (n + r) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_chunks {α : Type} : ∀ (f : Nat) (l : List α), l.length ≤ 16 * f → ∀ q,
    (chunks f l).getD q [] = (l.drop (16 * q)).take 16
  | 0, l, h, q => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [chunks]
  | f + 1, l, h, q => by
    unfold chunks
    cases hl : l.isEmpty
    · simp only [cond_false]
      rcases q with _ | q
      · simp
      · rw [List.getD_cons_succ, getD_chunks f (l.drop 16) (by simp; omega) q, List.drop_drop]
        congr 2
        omega
    · simp only [cond_true]
      have : l = [] := List.isEmpty_iff.1 hl
      subst this
      simp

theorem length_chunks_le {α : Type} : ∀ (f : Nat) (l : List α), (chunks f l).length ≤ f
  | 0, _ => by simp [chunks]
  | f + 1, l => by
    unfold chunks
    cases l.isEmpty
    · simp only [cond_false, List.length_cons]
      have := length_chunks_le f (l.drop 16)
      omega
    · simp

theorem getT_chunks {α : Type} (l : List α) (t : Nat) (d : α) :
    getT (chunks l.length (chunks l.length l)) t d = l.getD t d := by
  have h1 : (chunks l.length l).length ≤ 16 * l.length := by
    have := length_chunks_le l.length l
    omega
  unfold getT
  rw [getD_chunks _ _ h1, getD_take _ (Nat.mod_lt _ (by norm_num)), getD_drop,
    getD_chunks _ _ (by omega), getD_take _ (Nat.mod_lt _ (by norm_num)), getD_drop]
  congr 1
  have := Nat.div_add_mod t 16
  have := Nat.div_add_mod (t / 16) 16
  have : t / 16 / 16 = t / 256 := by rw [Nat.div_div_eq_div_mul]
  omega

theorem getT_of_treeOK {α : Type} [BEq α] [LawfulBEq α] {T : List (List (List α))} {l : List α}
    (h : treeOK T l = true) (t : Nat) (d : α) : getT T t d = l.getD t d := by
  rw [beq_iff_eq.mp h, getT_chunks]

theorem lt_pow {x k : Nat} (hx : x < 256) (hk : 8 ≤ k) : x < 2 ^ k := by
  have : (256 : Nat) ≤ 2 ^ k :=
    calc (256 : Nat) = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem fieldR_packR : ∀ {l : List Nat}, (∀ x ∈ l, x < 256) → ∀ j, fieldR (packR l) j = l.getD j 0
  | [], _, j => by simp [fieldR, packR]
  | x :: l, h, j => by
    have hx := h x List.mem_cons_self
    have ih := fieldR_packR (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    rcases j with _ | j
    · simp only [fieldR, packR, Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hk : k < 8
      · have : (255 : Nat).testBit k = true := by
          rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simpa using hk
        simp [this, show ¬ 8 ≤ k by omega]
      · have h255 : (255 : Nat).testBit k = false := by
          rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simpa using hk
        have hxk : x.testBit k = false := Nat.testBit_eq_false_of_lt (lt_pow hx (by omega))
        simp [h255, hxk]
    · rw [List.getD_cons_succ, ← ih j]
      simp only [fieldR, packR]
      congr 1
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
      have hxk : x.testBit (8 * (j + 1) + k) = false :=
        Nat.testBit_eq_false_of_lt (lt_pow hx (by omega))
      rw [hxk, Bool.false_or]
      have : 8 ≤ 8 * (j + 1) + k := by omega
      simp only [this, decide_true, Bool.true_and]
      congr 1
      omega

theorem tbit_eq (m i : Nat) : tbit m i = m.testBit i := by
  unfold tbit Nat.testBit
  rw [Nat.and_comm 1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> simp [h] <;> rfl

theorem bitsR_eq (m : Nat) : ∀ (n i : Nat), bitsR m n i = (List.range' i n).filter m.testBit
  | 0, _ => rfl
  | n + 1, i => by
    rw [bitsR, List.range'_succ, List.filter_cons, tbit_eq, bitsR_eq m n (i + 1)]
    cases m.testBit i <;> rfl

theorem prodR_eq (r : Nat) : ∀ (bs : List Nat) (acc : Nat),
    prodR r bs acc = bs.foldl (fun a j => a ||| (1 <<< fieldR r j)) acc
  | [], _ => rfl
  | j :: l, acc => by
    rw [prodR, prodR_eq r l, List.foldl_cons]
    rfl

theorem countR_eq (X : Nat) : ∀ (l : List Nat), countR X l = (l.filter X.testBit).length
  | [] => rfl
  | c :: l => by
    rw [countR, tbit_eq, List.filter_cons, countR_eq X l]
    cases X.testBit c <;> rfl

theorem extsGo_eq (m : Nat) (bs : List Nat) :
    ∀ (cs rs : List Nat) (k : Nat), cs.length = rs.length →
      extsGo m bs k cs rs = ((List.range' k cs.length).filter fun i =>
          !m.testBit i && Nat.beq (m &&& cs.getD (i - k) 0) m).map fun i =>
        bs.foldl (fun a j => a ||| (1 <<< fieldR (rs.getD (i - k) 0) j)) (m ||| (1 <<< i))
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | c :: cs, r :: rs, k, h => by
    have ih := extsGo_eq m bs cs rs (k + 1) (by simpa using h)
    have hfil : ((List.range' (k + 1) cs.length).filter fun i =>
        !m.testBit i && Nat.beq (m &&& (c :: cs).getD (i - k) 0) m) =
        ((List.range' (k + 1) cs.length).filter fun i =>
        !m.testBit i && Nat.beq (m &&& cs.getD (i - (k + 1)) 0) m) := by
      apply List.filter_congr
      intro i hi
      have hik : k + 1 ≤ i := (List.mem_range'_1.1 hi).1
      rw [show i - k = (i - (k + 1)) + 1 by omega, List.getD_cons_succ]
    have hrest : ((List.range' (k + 1) cs.length).filter fun i =>
        !m.testBit i && Nat.beq (m &&& (c :: cs).getD (i - k) 0) m).map
          (fun i => bs.foldl (fun a j => a ||| (1 <<< fieldR ((r :: rs).getD (i - k) 0) j))
            (m ||| (1 <<< i))) =
        extsGo m bs (k + 1) cs rs := by
      rw [ih, hfil]
      apply List.map_congr_left
      intro i hi
      have hik : k + 1 ≤ i := (List.mem_range'_1.1 (List.mem_filter.1 hi).1).1
      rw [show i - k = (i - (k + 1)) + 1 by omega, List.getD_cons_succ]
    rw [List.length_cons, List.range'_succ, List.filter_cons]
    have hk0 : (c :: cs).getD (k - k) 0 = c := by rw [Nat.sub_self]; rfl
    have hr0 : (r :: rs).getD (k - k) 0 = r := by rw [Nat.sub_self]; rfl
    change (bif !tbit m k && Nat.beq (Nat.land m c) m then
        prodR r bs (Nat.lor m (Nat.shiftLeft 1 k)) :: extsGo m bs (k + 1) cs rs
      else extsGo m bs (k + 1) cs rs) = _
    rw [hk0, tbit_eq, prodR_eq]
    cases hc : (!m.testBit k && Nat.beq (m &&& c) m)
    · simp only [cond_false, Bool.false_eq_true, if_false]
      exact hrest.symm
    · simp only [cond_true, if_true, List.map_cons, hr0]
      rw [hrest]
      rfl

theorem entriesEq_spec {T : List (List (List Nat))} {n : Nat} :
    ∀ {xs ts : List Nat}, entriesEq T n xs ts = true →
      xs.length = ts.length ∧ ∀ k (h : k < xs.length) (h' : k < ts.length),
        ts[k] < n ∧ xs[k] = getT T ts[k] 0
  | [], [], _ => ⟨rfl, fun k h => by simp at h⟩
  | [], _ :: _, h => by simp [entriesEq] at h
  | _ :: _, [], h => by simp [entriesEq] at h
  | x :: xs, t :: ts, h => by
    simp only [entriesEq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨ih1, ih2⟩ := entriesEq_spec h.2
    refine ⟨by simp [ih1], fun k hk hk' => ?_⟩
    rcases k with _ | k
    · exact ⟨h.1.1, h.1.2⟩
    · exact ih2 k (by simpa using hk) (by simpa using hk')

theorem foldl_or_testBit (t : Nat) :
    ∀ (l : List Nat) (a : Nat), (l.foldl (fun a s => a ||| (1 <<< s)) a).testBit t = true ↔
      a.testBit t = true ∨ t ∈ l
  | [], a => by simp
  | s :: l, a => by
    rw [List.foldl_cons, foldl_or_testBit t l, Nat.testBit_or, Nat.one_shiftLeft,
      Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

theorem foldl_cover_testBit (t : Nat) :
    ∀ (TG : List (List Nat)) (a : Nat),
      (TG.foldl (fun acc l => l.foldl (fun a s => a ||| (1 <<< s)) acc) a).testBit t = true ↔
        a.testBit t = true ∨ ∃ l ∈ TG, t ∈ l
  | [], a => by simp
  | l :: TG, a => by
    rw [List.foldl_cons, foldl_cover_testBit t TG, foldl_or_testBit t l]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem coverOK_spec {N : Nat} {TG : List (List Nat)} (h : coverOK N TG = true) :
    ∀ t < N, ∃ l ∈ TG, t ∈ l := by
  simp only [coverOK, beq_iff_eq] at h
  intro t ht
  have hb : (2 ^ N - 1).testBit t = true := by rw [Nat.testBit_two_pow_sub_one]; simpa using ht
  rw [← h, Nat.testBit_and, Bool.and_eq_true, foldl_cover_testBit] at hb
  rcases hb.1 with hb | hb
  · simp at hb
  · exact hb

theorem levelOK_mem {CML PTP L L' : List Nat} {TG : List (List Nat)} {T LT : List (List (List Nat))}
    {TGT : List (List (List (List Nat)))} (hT : treeOK T L' = true) (hLT : treeOK LT L = true)
    (hTGT : treeOK TGT TG = true) (hlen : TG.length = L.length)
    (hcov : coverOK L'.length TG = true) {nc : Nat} (hnc : L.length ≤ 128 * nc)
    (hcc : ∀ c < nc, closeChunk CML PTP T L'.length LT TGT L.length c = true) (m : Nat) :
    (∃ m0 ∈ L, m ∈ extsK CML PTP m0) ↔ m ∈ L' := by
  have hT' : T = chunks L'.length (chunks L'.length L') := beq_iff_eq.mp hT
  subst hT'
  have hcl : ∀ p (hp : p < L.length) (hp' : p < TG.length),
      entriesEq (chunks L'.length (chunks L'.length L')) L'.length (extsK CML PTP L[p]) TG[p] =
        true := by
    intro p hp hp'
    have hc : p / 128 < nc := by
      rcases Nat.lt_or_ge (p / 128) nc with h' | h'
      · exact h'
      · exfalso
        have : 128 * nc ≤ 128 * (p / 128) := Nat.mul_le_mul_left 128 h'
        have := Nat.mul_div_le p 128
        omega
    have hmem : p ∈ List.range' (128 * (p / 128)) 128 := by
      rw [List.mem_range'_1]
      have := Nat.div_add_mod p 128
      have := Nat.mod_lt p (show 128 > 0 by norm_num)
      omega
    have h := hcc _ hc
    unfold closeChunk at h
    rw [List.all_eq_true] at h
    have h := h p hmem
    rw [Bool.or_eq_true, decide_eq_true_eq, getT_of_treeOK hLT, getT_of_treeOK hTGT,
      List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hp'] at h
    rcases h with h | h
    · omega
    · exact h
  constructor
  · rintro ⟨m0, hm0, hm⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hm0
    have hp' : p < TG.length := by rw [hlen]; exact hp
    obtain ⟨hl1, hl2⟩ := entriesEq_spec (hcl p hp hp')
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
    have hk' : k < TG[p].length := hl1 ▸ hk
    obtain ⟨ht, he⟩ := hl2 k hk hk'
    rw [he, getT_chunks, List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  · intro hm
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hm
    obtain ⟨l, hl, htl⟩ := coverOK_spec hcov t ht
    obtain ⟨p, hp', rfl⟩ := List.mem_iff_getElem.1 hl
    have hp : p < L.length := by rw [← hlen]; exact hp'
    obtain ⟨hl1, hl2⟩ := entriesEq_spec (hcl p hp hp')
    obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 htl
    have hk : k < (extsK CML PTP L[p]).length := hl1 ▸ hk'
    refine ⟨L[p], List.getElem_mem hp, ?_⟩
    obtain ⟨-, he⟩ := hl2 k hk hk'
    rw [getT_chunks, List.getD_eq_getElem _ _ ht] at he
    rw [← he]
    exact List.getElem_mem hk

set_option exponentiation.threshold 2048 in
theorem testBit_andAll (FBT : List (List (List Nat))) {c : Nat} (hc : c < 2048) :
    ∀ (bs : List Nat), (andAll FBT bs).testBit c = bs.all fun j => (getT FBT j 0).testBit c := by
  have key : ∀ (bs : List Nat) (a : Nat),
      (bs.foldl (fun acc j => acc &&& getT FBT j 0) a).testBit c =
        (a.testBit c && bs.all fun j => (getT FBT j 0).testBit c) := by
    intro bs
    induction bs with
    | nil => intro a; simp
    | cons j bs ih =>
      intro a
      rw [List.foldl_cons, ih, Nat.testBit_and, List.all_cons, Bool.and_assoc]
  intro bs
  unfold andAll
  rw [key, Nat.testBit_two_pow_sub_one, decide_eq_true hc, Bool.true_and]

theorem boundsChunk_spec {FBT : List (List (List Nat))} {FLLT : List (List (List (List Nat)))}
    {L : List Nat} {LT : List (List (List Nat))} (hLT : treeOK LT L = true) {nc : Nat}
    (hnc : L.length ≤ 512 * nc) (h : ∀ c < nc, boundsChunk FBT FLLT LT L.length c = true) :
    ∀ m ∈ L, m >>> 191 = 0 ∧ (m = 0 ∨ fixCntK FBT FLLT m * ((bitIdxK m).length + 1) ≤ 1024) := by
  intro m hm
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hm
  have hc : p / 512 < nc := by
    rcases Nat.lt_or_ge (p / 512) nc with h' | h'
    · exact h'
    · exfalso
      have : 512 * nc ≤ 512 * (p / 512) := Nat.mul_le_mul_left 512 h'
      have := Nat.mul_div_le p 512
      omega
  have hmem : p ∈ List.range' (512 * (p / 512)) 512 := by
    rw [List.mem_range'_1]
    have := Nat.div_add_mod p 512
    have := Nat.mod_lt p (show 512 > 0 by norm_num)
    omega
  have hb := h _ hc
  unfold boundsChunk at hb
  rw [List.all_eq_true] at hb
  have hb := hb p hmem
  rw [getT_of_treeOK hLT, List.getD_eq_getElem _ _ hp] at hb
  simp only [boundOK1, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hb
  rcases hb with hb | hb
  · omega
  · exact hb

end CFSG.KC.J4Fam
