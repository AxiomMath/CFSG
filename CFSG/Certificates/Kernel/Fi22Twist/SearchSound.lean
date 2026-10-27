module

public import Certificates.Data.Kernel.Fi22Twist.Search
public import CFSG.Certificates.Kernel.PackSetSound

public section

set_option maxRecDepth 400000

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def csOf (a : Nat → Nat) : Nat :=
  Nat.lor (Nat.lor (a (bp 0)) (Nat.shiftLeft (a (bp 1)) 12)) (Nat.shiftLeft (a (bp 2)) 24)

@[expose] noncomputable def passK (M Dj BF : Nat → Nat) (H3 H4 m3 m4 cs : Nat) (a : Nat → Nat)
    (k p : Nat) : Bool :=
  (Nat.beq (fld(m3, a (fld(BF k, 0, 4095)), 1)) 1 &&
    relK Dj H3 (Nat.lor cs (Nat.shiftLeft (a (fld(BF k, 0, 4095))) 36))) &&
  (Nat.beq (fld(m4, a (fld(BF k, 12 * (p + 1), 4095)), 1)) 1 &&
    (relK Dj H4 (Nat.lor (Nat.lor cs (Nat.shiftLeft (a (fld(BF k, 0, 4095))) 36))
      (Nat.shiftLeft (a (fld(BF k, 12 * (p + 1), 4095))) 48)) &&
    g4K M Dj (a (fld(BF k, 0, 4095))) (a (fld(BF k, 12 * (p + 1), 4095)))))

@[expose] def codeMem (W x : Nat) : Prop := ∃ i, fld(W, 14 * i, 16383) = x

theorem push_fld_succ (s c i : Nat) (hc : c < 2 ^ 14) :
    fld(Nat.lor (Nat.shiftLeft s 14) c, 14 * (i + 1), 16383) = fld(s, 14 * i, 16383) := by
  change ((s <<< 14 ||| c) >>> (14 * (i + 1))) &&& (2 ^ 14 - 1) = (s >>> (14 * i)) &&& (2 ^ 14 - 1)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))]
  have e : 14 * (i + 1) + j - 14 = 14 * i + j := by omega
  have g : (14 * (i + 1) + j ≥ 14) = True := by simp only [ge_iff_le, eq_iff_iff, iff_true]; omega
  simp [e, g]

theorem push_fld_zero (s c : Nat) (hc : c < 2 ^ 14) :
    fld(Nat.lor (Nat.shiftLeft s 14) c, 14 * 0, 16383) = c := by
  change ((s <<< 14 ||| c) >>> (14 * 0)) &&& (2 ^ 14 - 1) = c
  rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hj : j < 14
  · simp [hj]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hj]

theorem codeMem_push {s x c : Nat} (hc : c < 2 ^ 14) (h : codeMem s x) :
    codeMem (Nat.lor (Nat.shiftLeft s 14) c) x := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i + 1, by rw [push_fld_succ s c i hc, hi]⟩

theorem brec_pres {P : Nat → Prop} {c : Bool} {e t : Nat} (he : P e) (ht : P t) :
    P (Bool.rec (motive := fun _ => Nat) e t c) := by
  cases c
  · exact he
  · exact ht

theorem brec_true {P : Nat → Prop} {c : Bool} {e t : Nat} (hc : c = true) (ht : P t) :
    P (Bool.rec (motive := fun _ => Nat) e t c) := by
  subst hc
  exact ht

theorem foldr_pres {P : Nat → Prop} {f : Nat → Nat → Nat} :
    ∀ {l : List Nat}, (∀ i ∈ l, ∀ s, P s → P (f i s)) → ∀ s, P s → P (l.foldr f s)
  | [], _, _, hs => hs
  | a :: l, hf, s, hs => hf a List.mem_cons_self _
      (foldr_pres (fun i hi => hf i (List.mem_cons_of_mem a hi)) s hs)

theorem foldr_mem {P : Nat → Prop} {f : Nat → Nat → Nat} {k : Nat} :
    ∀ {l : List Nat}, (∀ i ∈ l, ∀ s, P s → P (f i s)) → k ∈ l → (∀ s, P (f k s)) →
      ∀ s, P (l.foldr f s)
  | [], _, hk, _, _ => absurd hk List.not_mem_nil
  | a :: l, hf, hk, hadd, s => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hk with rfl | hk
    · exact hadd _
    · exact hf a List.mem_cons_self _
        (foldr_mem (fun i hi => hf i (List.mem_cons_of_mem a hi)) hk hadd s)

theorem code_lt {k p : Nat} (hk : k < 720) (hp : p < 8) : 8 * k + p + 1 < 2 ^ 14 := by
  have e : (2 : Nat) ^ 14 = 16384 := rfl
  omega

theorem stepK_pres (M Dj : Nat → Nat) (H3 H4 m3 m4 cs : Nat) (a : Nat → Nat) {k : Nat}
    (hk : k < 720) (ob : Nat) {s x : Nat} (hs : codeMem s x) :
    codeMem (stepK M Dj H3 H4 m3 m4 cs a k ob s) x := by
  unfold stepK
  rw [CFSG.KC.Pack.strictN_eq]
  refine brec_pres (P := fun s => codeMem s x) hs ?_
  dsimp only
  rw [CFSG.KC.Pack.foldBlk_eq]
  refine foldr_pres (P := fun s => codeMem s x) (fun l hl s2 hs2 => ?_) s hs
  rw [CFSG.KC.Pack.strictN_eq]
  refine brec_pres (P := fun s => codeMem s x) hs2 (codeMem_push ?_ hs2)
  exact code_lt hk (List.mem_range.1 (by simpa using hl))

theorem survK_sound (M Dj BF : Nat → Nat) (H3 H4 t0 t1 t2 k p : Nat) (hk : k < 720) (hp : p < 8)
    (h : passK M Dj BF H3 H4 (maskL M Dj (csOf fun x => ap t0 (ap t1 (ap t2 x))) 3 3)
      (maskL M Dj (csOf fun x => ap t0 (ap t1 (ap t2 x))) 3 4)
      (csOf fun x => ap t0 (ap t1 (ap t2 x))) (fun x => ap t0 (ap t1 (ap t2 x))) k p = true) :
    codeMem (survK M Dj BF H3 H4 t0 t1 t2) (8 * k + p + 1) := by
  unfold passK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, hC, hD, hE⟩ := h
  unfold survK
  simp only [CFSG.KC.Pack.strictN_eq]
  rw [CFSG.KC.Pack.foldN_eq]
  refine foldr_mem (P := fun s => codeMem s (8 * k + p + 1))
    (fun i hi s hs => stepK_pres _ _ _ _ _ _ _ _ (List.mem_range.1 hi) _ hs)
    (List.mem_range.2 hk) (fun s => ?_) 0
  unfold stepK
  rw [CFSG.KC.Pack.strictN_eq]
  refine brec_true (P := fun s => codeMem s (8 * k + p + 1))
    (CFSG.KC.Pack.band_iff.2 ⟨hA, hB⟩) ?_
  dsimp only
  rw [CFSG.KC.Pack.foldBlk_eq]
  refine foldr_mem (P := fun s => codeMem s (8 * k + p + 1)) (k := p)
    (fun l hl s2 hs2 => ?_) (List.mem_range.2 hp) (fun s2 => ?_) s
  · rw [CFSG.KC.Pack.strictN_eq]
    refine brec_pres (P := fun s => codeMem s (8 * k + p + 1)) hs2 (codeMem_push ?_ hs2)
    exact code_lt hk (List.mem_range.1 (by simpa using hl))
  · have e0 : nat_lit 0 + p = p := Nat.zero_add p
    rw [e0, CFSG.KC.Pack.strictN_eq]
    refine brec_true (P := fun s => codeMem s (8 * k + p + 1))
      (CFSG.KC.Pack.band_iff.2 ⟨hC, CFSG.KC.Pack.band_iff.2 ⟨hD, hE⟩⟩) ?_
    exact ⟨0, push_fld_zero _ _ (code_lt hk hp)⟩

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem blockK_eq (T D M BF H K : Nat → Nat) (j n : Nat) :
    blockK T D M BF H K j n = Nat.beq (survK M (fun e => D (Nat.add (Nat.mul 27 j) e)) BF
      (fld(H j, 0, Nat.sub (Nat.shiftLeft 1 256) 1)) (Nat.shiftRight (H j) 256)
      (T (fld(K n, 0, 65535))) (T (fld(K n, 16, 65535))) (T (fld(K n, 32, 65535))))
      (Nat.shiftRight (K n) 48) := by
  simp only [blockK, strictB_eq]

theorem blockK_sound {T D M BF H K : Nat → Nat} {j n : Nat}
    (hb : blockK T D M BF H K j n = true) (k p : Nat) (hk : k < 720) (hp : p < 8)
    (h : passK M (fun e => D (Nat.add (Nat.mul 27 j) e)) BF
      (fld(H j, 0, Nat.sub (Nat.shiftLeft 1 256) 1)) (Nat.shiftRight (H j) 256)
      (maskL M (fun e => D (Nat.add (Nat.mul 27 j) e))
        (csOf fun x => ap (T (fld(K n, 0, 65535))) (ap (T (fld(K n, 16, 65535)))
          (ap (T (fld(K n, 32, 65535))) x))) 3 3)
      (maskL M (fun e => D (Nat.add (Nat.mul 27 j) e))
        (csOf fun x => ap (T (fld(K n, 0, 65535))) (ap (T (fld(K n, 16, 65535)))
          (ap (T (fld(K n, 32, 65535))) x))) 3 4)
      (csOf fun x => ap (T (fld(K n, 0, 65535))) (ap (T (fld(K n, 16, 65535)))
        (ap (T (fld(K n, 32, 65535))) x)))
      (fun x => ap (T (fld(K n, 0, 65535))) (ap (T (fld(K n, 16, 65535)))
        (ap (T (fld(K n, 32, 65535))) x))) k p = true) :
    codeMem (Nat.shiftRight (K n) 48) (8 * k + p + 1) := by
  rw [blockK_eq] at hb
  rw [← Nat.eq_of_beq_eq_true hb]
  exact survK_sound _ _ _ _ _ _ _ _ k p hk hp h

theorem fld_bit (x v : Nat) : fld(x, v, 1) = (x.testBit v).toNat := by
  change (x >>> v) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ v) with h | h <;> simp [h]

theorem fullM_bit (v : Nat) : fullM.testBit v = decide (v < 3510) := by
  have h : ∀ n, ((1 <<< n) - 1).testBit v = decide (v < n) := fun n => by
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  exact h 3510

theorem maskL_step {s R E v : Nat} (hE : E < 2) (hv : v < 3510) :
    (Bool.rec (motive := fun _ => Nat) (Nat.land s (Nat.xor fullM R)) (Nat.land s R)
      (Nat.beq E 1)).testBit v = true ↔ s.testBit v = true ∧ fld(R, v, 1) = E := by
  rw [fld_bit]
  cases hc : Nat.beq E 1
  · have hE0 : E = 0 := by
      have := Nat.ne_of_beq_eq_false hc
      omega
    change (s &&& (fullM ^^^ R)).testBit v = true ↔ _
    rw [Nat.testBit_and, Nat.testBit_xor, fullM_bit, decide_eq_true hv, hE0]
    cases s.testBit v <;> cases R.testBit v <;> decide
  · have hE1 : E = 1 := Nat.eq_of_beq_eq_true hc
    change (s &&& R).testBit v = true ↔ _
    rw [Nat.testBit_and, hE1]
    cases s.testBit v <;> cases R.testBit v <;> decide

theorem foldr_testBit {F : Nat → Nat → Nat} {T : Nat → Prop} {v : Nat}
    (hF : ∀ r s, (F r s).testBit v = true ↔ s.testBit v = true ∧ T r) :
    ∀ (L : List Nat) (s : Nat),
      (L.foldr F s).testBit v = true ↔ s.testBit v = true ∧ ∀ r ∈ L, T r
  | [], s => by simp
  | r :: L, s => by
    rw [List.foldr_cons, hF, foldr_testBit hF L s]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem maskL_bit (M Dj : Nat → Nat) (cs nm i v : Nat) (hv : v < 3510) :
    fld(maskL M Dj cs nm i, v, 1) = 1 ↔
      ∀ m < nm, ∀ e < 27, eb M (ap (Dj e) (cg cs m)) v = eb M (ap (Dj e) (bp m)) (bp i) := by
  rw [fld_bit, Bool.toNat_eq_one]
  unfold maskL
  rw [CFSG.KC.Pack.foldN_eq]
  refine Iff.trans (foldr_testBit (T := fun r =>
    eb M (ap (Dj (r % 27)) (cg cs (r / 27))) v = eb M (ap (Dj (r % 27)) (bp (r / 27))) (bp i))
    ?_ _ _) ?_
  · intro r s
    have hE : eb M (ap (Dj (r % 27)) (bp (r / 27))) (bp i) < 2 := by
      unfold eb
      rw [fld_bit]
      exact Bool.toNat_lt _
    exact maskL_step hE hv
  · rw [fullM_bit, decide_eq_true hv]
    constructor
    · rintro ⟨-, h⟩ m hm e he
      have hr : 27 * m + e < 27 * nm := by omega
      have h1 : (27 * m + e) / 27 = m := by omega
      have h2 : (27 * m + e) % 27 = e := by omega
      have := h (27 * m + e) (List.mem_range.2 hr)
      rwa [h1, h2] at this
    · intro h
      refine ⟨rfl, fun r hr => ?_⟩
      have hr' : r < 27 * nm := List.mem_range.1 hr
      exact h (r / 27) (by omega) (r % 27) (Nat.mod_lt _ (by omega))

theorem allBlk_intro {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_intro fun l hl => h l (by omega)]

@[expose] noncomputable def relU (H t : Nat) : Nat := fld(H, Nat.add 8 (Nat.mul 16 t), 65535)

@[expose] noncomputable def relL (u : Nat) : Nat := Nat.land u 15

@[expose] noncomputable def relL2 (u : Nat) : Nat := fld(u, 4, 15)

@[expose] noncomputable def relE (u : Nat) : Nat := Nat.shiftRight u 8

@[expose] def RelV (Dj : Nat → Nat) (H lv : Nat) : Prop :=
  ∀ t < Nat.land H 255, relL (relU H t) ≤ lv ∧ relL2 (relU H t) ≤ lv ∧ relE (relU H t) < 27 ∧
    ap (Dj (relE (relU H t))) (bp (relL (relU H t))) = bp (relL2 (relU H t))

theorem relK_intro {Dj : Nat → Nat} {H cs lv : Nat} {g : Nat → Nat} (hR : RelV Dj H lv)
    (hc : ∀ l ≤ lv, cg cs l = g (bp l))
    (hD : ∀ e < 27, ∀ l ≤ lv, g (ap (Dj e) (bp l)) = ap (Dj e) (g (bp l))) :
    relK Dj H cs = true := by
  unfold relK
  refine allBlk_intro fun t ht => ?_
  change Nat.beq (cg cs (relL2 (relU H (Nat.add 0 t))))
    (ap (Dj (relE (relU H (Nat.add 0 t)))) (cg cs (relL (relU H (Nat.add 0 t))))) = true
  have e0 : Nat.add 0 t = t := Nat.zero_add t
  rw [e0]
  obtain ⟨h1, h2, h3, h4⟩ := hR t ht
  rw [hc _ h2, hc _ h1, ← h4, hD _ h3 _ h1]
  exact Nat.beq_refl _

theorem or_shift {A x s : Nat} (hA : A < 2 ^ s) : A ||| x <<< s = A + x * 2 ^ s := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hA, Nat.shiftLeft_eq, Nat.add_comm]

theorem cg_eq (N l : Nat) : cg N l = N / 2 ^ (12 * l) % 4096 := by
  have e : (4095 : Nat) = 2 ^ 12 - 1 := rfl
  change (N >>> (12 * l)) &&& 4095 = _
  rw [e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem cs_eq {x0 x1 x2 : Nat} (h0 : x0 < 4096) (h1 : x1 < 4096) :
    Nat.lor (Nat.lor x0 (Nat.shiftLeft x1 12)) (Nat.shiftLeft x2 24) =
      x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 := by
  change (x0 ||| x1 <<< 12) ||| x2 <<< 24 = _
  have a0 : x0 < 2 ^ 12 := by simp only [Nat.reducePow]; omega
  rw [or_shift a0]
  have a1 : x0 + x1 * 2 ^ 12 < 2 ^ 24 := by simp only [Nat.reducePow]; omega
  rw [or_shift a1]

theorem cg_pack {x0 x1 x2 x3 x4 : Nat} (h0 : x0 < 4096) (h1 : x1 < 4096) (h2 : x2 < 4096)
    (h3 : x3 < 4096) (h4 : x4 < 4096) :
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 + x4 * 2 ^ 48) 0 = x0 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 + x4 * 2 ^ 48) 1 = x1 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 + x4 * 2 ^ 48) 2 = x2 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 + x4 * 2 ^ 48) 3 = x3 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 + x4 * 2 ^ 48) 4 = x4 := by
  simp only [cg_eq, Nat.reducePow, Nat.reduceMul]
  omega

theorem cg_pack3 {x0 x1 x2 : Nat} (h0 : x0 < 4096) (h1 : x1 < 4096) (h2 : x2 < 4096) :
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24) 0 = x0 ∧ cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24) 1 = x1 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24) 2 = x2 := by
  simp only [cg_eq, Nat.reducePow, Nat.reduceMul]
  omega

theorem cg_pack4 {x0 x1 x2 x3 : Nat} (h0 : x0 < 4096) (h1 : x1 < 4096) (h2 : x2 < 4096)
    (h3 : x3 < 4096) :
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36) 0 = x0 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36) 1 = x1 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36) 2 = x2 ∧
    cg (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36) 3 = x3 := by
  simp only [cg_eq, Nat.reducePow, Nat.reduceMul]
  omega

theorem pack4 {x0 x1 x2 x3 : Nat} (h0 : x0 < 4096) (h1 : x1 < 4096) (h2 : x2 < 4096) :
    Nat.lor (Nat.lor (Nat.lor x0 (Nat.shiftLeft x1 12)) (Nat.shiftLeft x2 24))
      (Nat.shiftLeft x3 36) = x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 := by
  rw [cs_eq h0 h1]
  change (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24) ||| x3 <<< 36 = _
  have a2 : x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 < 2 ^ 36 := by simp only [Nat.reducePow]; omega
  rw [or_shift a2]

theorem pack5 {x0 x1 x2 x3 x4 : Nat} (h0 : x0 < 4096) (h1 : x1 < 4096) (h2 : x2 < 4096)
    (h3 : x3 < 4096) :
    Nat.lor (Nat.lor (Nat.lor (Nat.lor x0 (Nat.shiftLeft x1 12)) (Nat.shiftLeft x2 24))
      (Nat.shiftLeft x3 36)) (Nat.shiftLeft x4 48) =
      x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 + x4 * 2 ^ 48 := by
  rw [pack4 h0 h1 h2]
  change (x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36) ||| x4 <<< 48 = _
  have a3 : x0 + x1 * 2 ^ 12 + x2 * 2 ^ 24 + x3 * 2 ^ 36 < 2 ^ 48 := by
    simp only [Nat.reducePow]; omega
  rw [or_shift a3]

theorem bp0 : bp 0 = 0 := rfl
theorem bp1 : bp 1 = 1 := rfl
theorem bp2 : bp 2 = 2 := rfl
theorem bp3 : bp 3 = 3 := rfl
theorem bp4 : bp 4 = 6 := rfl

theorem bp_lt (l : Nat) (hl : l ≤ 4) : bp l < 3510 := by
  obtain rfl | rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
  all_goals decide

theorem mask_of_map {M Dj : Nat → Nat} {a g : Nat → Nat}
    (hg : ∀ x < 3510, g x < 3510)
    (hadj : ∀ x < 3510, ∀ y < 3510, eb M (g x) (g y) = eb M x y)
    (hD : ∀ e < 27, ∀ x < 3510, g (ap (Dj e) x) = ap (Dj e) (g x))
    (hDlt : ∀ e < 27, ∀ x < 3510, ap (Dj e) x < 3510)
    (c2 : ∀ m < 3, cg (csOf a) m = g (bp m)) (i : Nat) (hi : i ≤ 4) :
    fld(maskL M Dj (csOf a) 3 i, g (bp i), 1) = 1 := by
  rw [maskL_bit _ _ _ _ _ _ (hg _ (bp_lt i hi))]
  intro m hm e he
  rw [c2 m hm, ← hD e he _ (bp_lt m (by omega)),
    hadj _ (hDlt e he _ (bp_lt m (by omega))) _ (bp_lt i hi)]

theorem g4_of_map {M Dj : Nat → Nat} {g : Nat → Nat}
    (hadj : ∀ x < 3510, ∀ y < 3510, eb M (g x) (g y) = eb M x y)
    (hD : ∀ e < 27, ∀ x < 3510, g (ap (Dj e) x) = ap (Dj e) (g x))
    (hDlt : ∀ e < 27, ∀ x < 3510, ap (Dj e) x < 3510) :
    g4K M Dj (g 3) (g 6) = true := by
  unfold g4K
  refine allBlk_intro fun e he => ?_
  change Nat.beq (eb M (ap (Dj (Nat.add 0 e)) (g 3)) (g 6))
    (eb M (ap (Dj (Nat.add 0 e)) 3) 6) = true
  have e0 : Nat.add 0 e = e := Nat.zero_add e
  rw [e0]
  have h33 : (3 : Nat) < 3510 := by omega
  have h66 : (6 : Nat) < 3510 := by omega
  rw [← hD e he 3 h33, hadj _ (hDlt e he 3 h33) _ h66]
  exact Nat.beq_refl _

theorem pass_of_map {M Dj BF : Nat → Nat} {H3 H4 : Nat} {a g : Nat → Nat} {k p : Nat}
    (hR3 : RelV Dj H3 3) (hR4 : RelV Dj H4 4)
    (hg : ∀ x < 3510, g x < 3510)
    (hadj : ∀ x < 3510, ∀ y < 3510, eb M (g x) (g y) = eb M x y)
    (hD : ∀ e < 27, ∀ x < 3510, g (ap (Dj e) x) = ap (Dj e) (g x))
    (hDlt : ∀ e < 27, ∀ x < 3510, ap (Dj e) x < 3510)
    (c2 : ∀ m < 3, cg (csOf a) m = g (bp m))
    (c3 : ∀ l ≤ 3, cg (Nat.lor (csOf a) (Nat.shiftLeft (g 3) 36)) l = g (bp l))
    (c4 : ∀ l ≤ 4, cg (Nat.lor (Nat.lor (csOf a) (Nat.shiftLeft (g 3) 36))
      (Nat.shiftLeft (g 6) 48)) l = g (bp l))
    (h3 : a (fld(BF k, 0, 4095)) = g 3) (h4 : a (fld(BF k, 12 * (p + 1), 4095)) = g 6) :
    passK M Dj BF H3 H4 (maskL M Dj (csOf a) 3 3) (maskL M Dj (csOf a) 3 4) (csOf a) a k p =
      true := by
  have hDb : ∀ lv ≤ 4, ∀ e < 27, ∀ l ≤ lv, g (ap (Dj e) (bp l)) = ap (Dj e) (g (bp l)) :=
    fun lv hlv e he l hl => hD e he _ (bp_lt l (by omega))
  have m3 := mask_of_map hg hadj hD hDlt c2 3 (by omega)
  have m4 := mask_of_map hg hadj hD hDlt c2 4 (by omega)
  rw [bp3] at m3
  rw [bp4] at m4
  unfold passK
  rw [h3, h4, m3, m4, relK_intro hR3 c3 (hDb 3 (by omega)), relK_intro hR4 c4 (hDb 4 (by omega)),
    g4_of_map hadj hD hDlt]
  all_goals rfl

theorem pack_facts {a g : Nat → Nat} (ha : ∀ m < 3, a (bp m) = g (bp m))
    (hg : ∀ x < 3510, g x < 3510) :
    (∀ m < 3, cg (csOf a) m = g (bp m)) ∧
    (∀ l ≤ 3, cg (Nat.lor (csOf a) (Nat.shiftLeft (g 3) 36)) l = g (bp l)) ∧
    (∀ l ≤ 4, cg (Nat.lor (Nat.lor (csOf a) (Nat.shiftLeft (g 3) 36))
      (Nat.shiftLeft (g 6) 48)) l = g (bp l)) := by
  have l0 : g (bp 0) < 4096 := Nat.lt_trans (hg _ (bp_lt 0 (by omega))) (by omega)
  have l1 : g (bp 1) < 4096 := Nat.lt_trans (hg _ (bp_lt 1 (by omega))) (by omega)
  have l2 : g (bp 2) < 4096 := Nat.lt_trans (hg _ (bp_lt 2 (by omega))) (by omega)
  have l3 : g 3 < 4096 := Nat.lt_trans (hg 3 (by omega)) (by omega)
  have l4 : g 6 < 4096 := Nat.lt_trans (hg 6 (by omega)) (by omega)
  have e : csOf a = Nat.lor (Nat.lor (g (bp 0)) (Nat.shiftLeft (g (bp 1)) 12))
      (Nat.shiftLeft (g (bp 2)) 24) := by
    unfold csOf
    rw [ha 0 (by omega), ha 1 (by omega), ha 2 (by omega)]
  rw [e, pack5 l0 l1 l2 l3, pack4 l0 l1 l2, cs_eq l0 l1]
  obtain ⟨q0, q1, q2⟩ := cg_pack3 l0 l1 l2
  obtain ⟨r0, r1, r2, r3⟩ := cg_pack4 l0 l1 l2 l3
  obtain ⟨s0, s1, s2, s3, s4⟩ := cg_pack l0 l1 l2 l3 l4
  refine ⟨fun m hm => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    · exact q0
    · exact q1
    · exact q2
  · obtain rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
    · exact r0
    · exact r1
    · exact r2
    · rw [bp3]
      exact r3
  · obtain rfl | rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
    · exact s0
    · exact s1
    · exact s2
    · rw [bp3]
      exact s3
    · rw [bp4]
      exact s4

theorem pass_of_base {M Dj BF : Nat → Nat} {H3 H4 : Nat} {a g : Nat → Nat} {k p : Nat}
    (hR3 : RelV Dj H3 3) (hR4 : RelV Dj H4 4)
    (hg : ∀ x < 3510, g x < 3510)
    (hadj : ∀ x < 3510, ∀ y < 3510, eb M (g x) (g y) = eb M x y)
    (hD : ∀ e < 27, ∀ x < 3510, g (ap (Dj e) x) = ap (Dj e) (g x))
    (hDlt : ∀ e < 27, ∀ x < 3510, ap (Dj e) x < 3510)
    (ha : ∀ m < 3, a (bp m) = g (bp m))
    (h3 : a (fld(BF k, 0, 4095)) = g 3) (h4 : a (fld(BF k, 12 * (p + 1), 4095)) = g 6) :
    passK M Dj BF H3 H4 (maskL M Dj (csOf a) 3 3) (maskL M Dj (csOf a) 3 4) (csOf a) a k p =
      true :=
  have hp := pack_facts ha hg
  pass_of_map hR3 hR4 hg hadj hD hDlt hp.1 hp.2.1 hp.2.2 h3 h4

end CFSG.KC.Fi22Twist

end
