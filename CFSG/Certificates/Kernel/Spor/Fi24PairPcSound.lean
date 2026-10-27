module

public import Certificates.Data.Kernel.Spor.Fi24PairPc
public import CFSG.Certificates.Kernel.Common.PcPrimes
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import Certificates.Certificate1016Base

public section

namespace CFSG.KS.Fi24PairPc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24PairK CFSG.KC.Fi24PairPc CFSG.KC.PcPrimes
  CFSG.Sporadic.Th

local notation "J" => CFSG.Sporadic.Fi24.J

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem apZ_nil (NV : Nat → Nat → Nat) (x : Nat) : apZ NV [] x = x := rfl

theorem apZ_cons (NV : Nat → Nat → Nat) (z : Int) (w : List Int) (x : Nat) :
    apZ NV (z :: w) x = ptZ NV z (apZ NV w x) := by
  change strictN (apZ NV w x) (fun y => ptZ NV z y) = _
  rw [strictN_eq]

theorem apZ_append (NV : Nat → Nat → Nat) (u v : List Int) (x : Nat) :
    apZ NV (u ++ v) x = apZ NV u (apZ NV v x) := by
  induction u with
  | nil => rfl
  | cons z u ih => rw [List.cons_append, apZ_cons, apZ_cons, ih]

theorem dirOK_nil (net : Nat → Bool) : dirOK net [] = true := rfl

theorem dirOK_cons (net : Nat → Bool) (z : Int) (w : List Int) :
    dirOK net (z :: w) = (dirZ net z && dirOK net w) := andB_eq _ _

theorem dirOK_append (net : Nat → Bool) (u v : List Int) :
    dirOK net (u ++ v) = (dirOK net u && dirOK net v) := by
  induction u with
  | nil => rfl
  | cons z u ih => rw [List.cons_append, dirOK_cons, dirOK_cons, ih, Bool.and_assoc]

theorem invW_nil : invW [] = [] := rfl

theorem invW_cons (z : Int) (w : List Int) : invW (z :: w) = invW w ++ [-z] := rfl

theorem dirZ_neg (net : Nat → Bool) (z : Int) : dirZ net (-z) = dirZ net z := by
  unfold dirZ
  rw [Int.natAbs_neg]

theorem dirOK_invW (net : Nat → Bool) (w : List Int) : dirOK net (invW w) = dirOK net w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [invW_cons, dirOK_append, ih, dirOK_cons, dirOK_cons, dirOK_nil, dirZ_neg, Bool.and_true,
      Bool.and_comm]

theorem inR_spec {lo hi : Nat} {r : List Nat} (h : inR lo hi r = true) :
    ∀ i ∈ r, lo ≤ i ∧ i < hi := by
  induction r with
  | nil => simp
  | cons a r ih =>
    change andB (andB (Nat.ble lo a) (Nat.blt a hi)) (inR lo hi r) = true at h
    simp only [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    intro i hi'
    rcases List.mem_cons.1 hi' with rfl | hi'
    · exact h.1
    · exact ih h.2 i hi'

theorem eqZ_spec {NV : Nat → Nat → Nat} {u v : List Int} (h : eqZ NV u v = true) :
    ∀ b ∈ cbZ, apZ NV u b = apZ NV v b := by
  unfold eqZ cbZ at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, Bool.and_true] at h
  intro b hb
  simp only [cbZ, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2

theorem rep_spec (i : Nat) : ∀ e, rep i e = List.replicate e i
  | 0 => rfl
  | e + 1 => by
    change i :: rep i e = _
    rw [rep_spec i e, List.replicate_succ]

theorem pcW_nil (xs : List (List Nat)) : pcW xs [] = [] := rfl

theorem pcW_cons (xs : List (List Nat)) (i : Nat) (r : List Nat) :
    pcW xs (i :: r) = xW xs i ++ pcW xs r := rfl

theorem dec_ne_zero {c : Nat} (hc : 2 ≤ c) : dec c ≠ 0 := by
  unfold dec
  cases Nat.beq (Nat.mod c 2) 0
  · change -((c / 2 : ℕ) : ℤ) ≠ 0
    omega
  · change ((c / 2 : ℕ) : ℤ) ≠ 0
    omega

theorem mem_wdec {z : Int} : ∀ {w : List Nat}, z ∈ wdec w → ∃ c ∈ w, z = dec c
  | [], h => absurd h List.not_mem_nil
  | c :: w, h => by
    change z ∈ dec c :: wdec w at h
    rcases List.mem_cons.1 h with h | h
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨c', hc', e⟩ := mem_wdec h
      exact ⟨c', List.mem_cons_of_mem c hc', e⟩

theorem nthLL_mem : ∀ (l : List (List Nat)) (i : Nat), nthLL l i = [] ∨ nthLL l i ∈ l
  | [], _ => Or.inl rfl
  | _ :: _, 0 => Or.inr List.mem_cons_self
  | a :: l, i + 1 => by
    change nthLL l i = [] ∨ nthLL l i ∈ a :: l
    rcases nthLL_mem l i with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem a h)

theorem xW_ne_zero {xs : List (List Nat)}
    (h : (xs.all fun w => w.all fun c => Nat.ble 2 c) = true) : ∀ j z, z ∈ xW xs j → z ≠ 0 := by
  intro j z hz
  obtain ⟨c, hc, rfl⟩ := mem_wdec hz
  rcases nthLL_mem xs j with e | e
  · rw [e] at hc
    exact absurd hc List.not_mem_nil
  · exact dec_ne_zero (Nat.le_of_ble_eq_true ((List.all_eq_true.1 (List.all_eq_true.1 h _ e)) c hc))

section Words

variable (L : ℤ → J)

@[expose] noncomputable def wEl (w : List ℤ) : J := (w.map L).prod

theorem wEl_append (u v : List ℤ) : wEl L (u ++ v) = wEl L u * wEl L v := by
  unfold wEl
  rw [List.map_append, List.prod_append]

theorem wEl_cons (z : ℤ) (w : List ℤ) : wEl L (z :: w) = L z * wEl L w := by
  unfold wEl
  rw [List.map_cons, List.prod_cons]

theorem wEl_invW (hinv : ∀ z, z ≠ 0 → L (-z) = (L z)⁻¹) (w : List ℤ) (hw : ∀ z ∈ w, z ≠ 0) :
    wEl L (invW w) = (wEl L w)⁻¹ := by
  induction w with
  | nil => simp [wEl, invW_nil]
  | cons z w ih =>
    rw [invW_cons, wEl_append, ih fun y hy => hw y (List.mem_cons_of_mem z hy), wEl_cons, wEl_cons,
      mul_inv_rev, hinv z (hw z List.mem_cons_self)]
    simp [wEl]

@[expose] noncomputable def xg (xs : List (List Nat)) (i : ℕ) : J := wEl L (xW xs i)

theorem wEl_pcW (xs : List (List Nat)) (r : List Nat) :
    wEl L (pcW xs r) = (r.map (xg L xs)).prod := by
  induction r with
  | nil => simp [wEl, pcW_nil]
  | cons i r ih => rw [pcW_cons, wEl_append, ih, List.map_cons, List.prod_cons]; rfl

@[expose] def PtHyp (NV : Nat → Nat → Nat) (net : Nat → Bool) : Prop :=
  ∀ z, dirZ net z = true → ∀ q < 306936, ptZ NV z q = idx 306936 (L z) q

variable {L} {NV : Nat → Nat → Nat} {net : Nat → Bool}

theorem apZ_eq (hN : PtHyp L NV net) :
    ∀ w : List ℤ, dirOK net w = true → ∀ q < 306936, apZ NV w q = idx 306936 (wEl L w) q
  | [], _, q, _ => by rw [apZ_nil]; simp [wEl, idx_one]
  | z :: w, hw, q, hq => by
    rw [dirOK_cons, Bool.and_eq_true] at hw
    rw [apZ_cons, apZ_eq hN w hw.2 q hq, wEl_cons, idx_mul,
      hN z hw.1 _ (idx_lt _ hq)]

theorem chainBase_mem : ∀ t < CFSG.Sporadic.Fi24.Native.chainBase.size,
    CFSG.Sporadic.Fi24.Native.chainBase[t]! ∈ cbZ := by decide

theorem cbZ_lt : ∀ b ∈ cbZ, b < 306936 := by decide

theorem eq_of_eqZ (hN : PtHyp L NV net) {u v : List ℤ}
    (hu : dirOK net u = true) (hv : dirOK net v = true) (h : eqZ NV u v = true) :
    wEl L u = wEl L v := by
  have hgh : ∀ b ∈ cbZ, idx 306936 (wEl L u) b = idx 306936 (wEl L v) b := fun b hb => by
    rw [← apZ_eq hN u hu b (cbZ_lt b hb), ← apZ_eq hN v hv b (cbZ_lt b hb)]
    exact eqZ_spec h b hb
  have : (wEl L v)⁻¹ * wEl L u = 1 := CFSG.Sporadic.Fi24.sep _ fun t ht => by
    rw [idx_mul, hgh _ (chainBase_mem t ht), idx_inv_idx]
  rw [inv_mul_eq_one] at this
  exact this.symm

end Words

section Bound

variable {L : ℤ → J} {NV : Nat → Nat → Nat} {net : Nat → Bool} {xs : List (List Nat)}
  {ps : List Nat} {pw : List (List Nat)} {cj : List (List (List Nat))} {n : Nat}

theorem relOK_parts {j : Nat} (h : relOK NV net xs ps pw cj n j = true) :
    dirOK net (xW xs j) = true ∧ 0 < nthN ps j ∧ inR (j + 1) n (nthLL pw j) = true ∧
      eqZ NV (pcW xs (rep j (nthN ps j))) (pcW xs (nthLL pw j)) = true ∧
      lenA (nthL3 cj j) = n - (j + 1) ∧ cjOK NV xs n j (j + 1) (nthL3 cj j) = true := by
  unfold relOK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.sub_eq, Nat.succ_eq_add_one]
    at h
  exact ⟨h.1.1, h.1.2, h.2.1.1, h.2.1.2, h.2.2.1, h.2.2.2⟩

theorem lenA_eq {α : Type} (l : List α) : lenA l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => change Nat.succ (lenA l) = _; rw [ih]; rfl

theorem cjOK_spec {j : Nat} :
    ∀ (cs : List (List Nat)) (k : Nat), cjOK NV xs n j k cs = true → ∀ m < cs.length,
      inR (j + 1) n (nthLL cs m) = true ∧
        eqZ NV (invW (xW xs j) ++ (xW xs (k + m) ++ xW xs j)) (pcW xs (nthLL cs m)) = true
  | [], _, _, m, hm => absurd hm (by simp)
  | c :: cs, k, h, m, hm => by
    change bAnd(andB (inR (Nat.succ j) n c)
      (eqZ NV (invW (xW xs j) ++ (xW xs k ++ xW xs j)) (pcW xs c)), cjOK NV xs n j (k + 1) cs) = true
      at h
    simp only [bAnd_eq, andB_eq, Bool.and_eq_true] at h
    rcases m with _ | m
    · exact ⟨h.1.1, h.1.2⟩
    · have := cjOK_spec cs (k + 1) h.2 m (by simp at hm; omega)
      rw [show k + 1 + m = k + (m + 1) by omega] at this
      exact this

theorem cjOK_of {j : Nat} :
    ∀ (cs : List (List Nat)) (k : Nat),
      (∀ m < cs.length, cjOne NV xs n j (k + m) (nthLL cs m) = true) → cjOK NV xs n j k cs = true
  | [], _, _ => rfl
  | c :: cs, k, h => by
    change bAnd(andB (inR (Nat.succ j) n c)
      (eqZ NV (invW (xW xs j) ++ (xW xs k ++ xW xs j)) (pcW xs c)), cjOK NV xs n j (k + 1) cs) = true
    rw [bAnd_eq, Bool.and_eq_true]
    refine ⟨h 0 (by simp), cjOK_of cs (k + 1) fun m hm => ?_⟩
    have := h (m + 1) (by simp; omega)
    rwa [show k + (m + 1) = k + 1 + m by omega] at this

theorem pcCk_at {j k : Nat} (hk : k < n) :
    pcCk NV net xs ps pw cj n (n * j + k) =
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true (relHd NV net xs ps pw cj n j) (Nat.beq j k))
        (cjOne NV xs n j k (nthLL (nthL3 cj j) (Nat.sub k (Nat.succ j)))) (Nat.blt j k) := by
  have hn : 0 < n := by omega
  have hd : Nat.div (n * j + k) n = j := by
    change (n * j + k) / n = j
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hm : Nat.mod (n * j + k) n = k := by
    change (n * j + k) % n = k
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  unfold pcCk
  rw [hd, hm]

theorem relOK_of_pcCk (h : ∀ g < n * n, pcCk NV net xs ps pw cj n g = true) :
    ∀ j < n, relOK NV net xs ps pw cj n j = true := by
  intro j hj
  have hg : ∀ k < n, pcCk NV net xs ps pw cj n (n * j + k) = true := fun k hk =>
    h _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _)
      (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj))
  have hhd : relHd NV net xs ps pw cj n j = true := by
    have := hg j hj
    rw [pcCk_at hj, show Nat.blt j j = false by cases e : Nat.blt j j <;> simp_all [Nat.blt_eq],
      show Nat.beq j j = true from Nat.beq_refl j] at this
    exact this
  have hlen : lenA (nthL3 cj j) = n - (j + 1) := by
    unfold relHd at hhd
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.sub_eq, Nat.succ_eq_add_one] at hhd
    exact hhd.2.2
  have hcj : cjOK NV xs n j (j + 1) (nthL3 cj j) = true := by
    refine cjOK_of _ _ fun m hm => ?_
    rw [lenA_eq] at hlen
    have := hg (j + 1 + m) (by omega)
    rw [pcCk_at (by omega), show Nat.blt j (j + 1 + m) = true by simp [Nat.blt_eq]; omega,
      show Nat.sub (j + 1 + m) (Nat.succ j) = m by change j + 1 + m - (j + 1) = m; omega] at this
    exact this
  unfold relHd at hhd
  unfold relOK
  simp only [andB_eq, Bool.and_eq_true] at hhd ⊢
  exact ⟨hhd.1, ⟨hhd.2.1, hhd.2.2, hcj⟩⟩

theorem prod_mem_pcSub (hrel : ∀ j < n, relOK NV net xs ps pw cj n j = true)
    {i : Nat} {r : List Nat} (hr : ∀ m ∈ r, i ≤ m ∧ m < n) :
    (r.map (xg L xs)).prod ∈ pcSub (xg L xs) n i := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hg
  exact x_mem (hr m hm).1 (hr m hm).2

theorem dirOK_pcW (hrel : ∀ j < n, relOK NV net xs ps pw cj n j = true) :
    ∀ r : List Nat, (∀ m ∈ r, m < n) → dirOK net (pcW xs r) = true
  | [], _ => rfl
  | i :: r, hr => by
    rw [pcW_cons, dirOK_append, (relOK_parts (hrel i (hr i List.mem_cons_self))).1,
      dirOK_pcW hrel r fun m hm => hr m (List.mem_cons_of_mem _ hm), Bool.and_true]

theorem pcSeq (hN : PtHyp L NV net) (hinv : ∀ z, z ≠ 0 → L (-z) = (L z)⁻¹)
    (hnz : ∀ j z, z ∈ xW xs j → z ≠ 0) (hrel : ∀ j < n, relOK NV net xs ps pw cj n j = true) :
    PcSeq (xg L xs) (nthN ps) n := by
  refine ⟨fun j hj => (relOK_parts (hrel j hj)).2.1, fun j hj => ?_, fun j k hjk hk => ?_⟩
  · obtain ⟨hd, -, hr, he, -⟩ := relOK_parts (hrel j hj)
    have hr' := inR_spec hr
    have e := eq_of_eqZ hN (dirOK_pcW hrel _ fun m hm => by
        rw [rep_spec, List.mem_replicate] at hm; omega)
      (dirOK_pcW hrel _ fun m hm => (hr' m hm).2) he
    rw [wEl_pcW, wEl_pcW, rep_spec, List.map_replicate, List.prod_replicate] at e
    rw [e]
    exact prod_mem_pcSub hrel hr'
  · obtain ⟨hd, -, -, -, hlen, hc⟩ := relOK_parts (hrel j (by omega))
    rw [lenA_eq] at hlen
    have := cjOK_spec _ (j + 1) hc (k - (j + 1)) (by omega)
    rw [show j + 1 + (k - (j + 1)) = k by omega] at this
    obtain ⟨hr, he⟩ := this
    have hr' := inR_spec hr
    have hdk := (relOK_parts (hrel k hk)).1
    have e := eq_of_eqZ hN (by rw [dirOK_append, dirOK_append, dirOK_invW, hd, hdk]; rfl)
      (dirOK_pcW hrel _ fun m hm => (hr' m hm).2) he
    rw [wEl_append, wEl_append, wEl_invW L hinv _ (hnz j), wEl_pcW] at e
    change (xg L xs j)⁻¹ * (xg L xs k * xg L xs j) = _ at e
    rw [← mul_assoc] at e
    rw [e]
    exact prod_mem_pcSub hrel hr'

theorem card_le_of (hN : PtHyp L NV net) (hinv : ∀ z, z ≠ 0 → L (-z) = (L z)⁻¹)
    (hnz : ∀ j z, z ∈ xW xs j → z ≠ 0)
    (hrel : ∀ j < n, relOK NV net xs ps pw cj n j = true) {ls : List Nat}
    (hgen : ∀ l ∈ ls, ∃ r, genOK NV net xs n l r = true) :
    Nat.card (Subgroup.closure {g | ∃ l ∈ ls, g = L (Int.ofNat (l + 3))}) ≤
      ∏ j ∈ Finset.range n, nthN ps j := by
  refine le_trans (Subgroup.card_le_of_le ?_) (card_le (pcSeq hN hinv hnz hrel))
  refine (Subgroup.closure_le _).2 fun g ⟨l, hl, hg⟩ => ?_
  obtain ⟨r, h⟩ := hgen l hl
  unfold genOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨hnet, hr⟩, he⟩ := h
  have hr' := inR_spec hr
  have hd : dirOK net [Int.ofNat (Nat.add l 3)] = true := by
    rw [dirOK_cons, dirOK_nil, Bool.and_true]
    unfold dirZ
    rw [show (Int.ofNat (Nat.add l 3)).natAbs = l + 3 from rfl,
      show Nat.sub (l + 3) 3 = l from Nat.add_sub_cancel l 3, hnet]
    cases Nat.ble (l + 3) 2 <;> rfl
  have e := eq_of_eqZ hN hd (dirOK_pcW hrel _ fun m hm => (hr' m hm).2) he
  rw [wEl_pcW, wEl_cons] at e
  simp only [wEl, List.map_nil, List.prod_nil, mul_one] at e
  rw [hg]
  change L (Int.ofNat (Nat.add l 3)) ∈ _
  rw [e]
  exact prod_mem_pcSub hrel fun m hm => ⟨Nat.zero_le _, (hr' m hm).2⟩

end Bound

end CFSG.KS.Fi24PairPc

end
