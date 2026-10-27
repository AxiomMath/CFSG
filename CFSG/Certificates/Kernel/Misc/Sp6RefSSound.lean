module

public import Certificates.Data.Kernel.Misc.Sp6RefS
public import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KC.Misc.Sp6RefS

open CFSG.KD.Sp62 CFSG.KD.Sp6RefS CFSG.KC.Loop CFSG.KC.Misc.Clos

theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KD.Sp6A2.strictB y k = k y := by
  cases y <;> rfl

theorem commB_iff {a b : Nat} : commB a b = true ↔ MULF a b = MULF b a := by
  rw [commB, Nat.beq_eq]

private theorem bAnd_eq (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem recAll_iff (g : Nat → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
        (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n = true ↔
      ∀ k < n, g k = true
  | 0 => by simp
  | n + 1 => by
    change Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n) (g n) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, recAll_iff g n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h2 k h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem allBelow_sound {m hi : Nat} {f : Nat → Bool} (hm : m ≤ 64 * hi)
    (h : allBelow m hi f = true) : ∀ i < m, f i = true := by
  unfold allBelow at h
  rw [recAll_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64) hi] at h
  intro i hi'
  have h1 := h (i / 64) (by omega)
  rw [recAll_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
    (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64] at h1
  have h2 := h1 (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have h3 : Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m) = true := by
    simpa only [e] using h2
  rw [Nat.blt_eq.mpr hi'] at h3
  exact h3

theorem aK_sound {G : Type*} [Group G] {enc : G → Nat} (henc : ClosEnc enc MULF ONE)
    {z : Fin 3 → G} {Z A : Nat → Nat} (hZ : ∀ i : Fin 3, Z i = enc (z i)) (h : aK Z A = true) :
    ∀ a < 3, ∀ b < 3, ∀ c < 3, A (9 * a + 3 * b + c) = enc (z 0 ^ a * z 1 ^ b * z 2 ^ c) := by
  simp only [aK, Bool.and_eq_true] at h
  obtain ⟨h0, hs⟩ := h
  have hst := allBelow_sound (by decide) hs
  have hZ0 : Z 0 = enc (z 0) := hZ 0
  have hZ1 : Z 1 = enc (z 1) := hZ 1
  have hZ2 : Z 2 = enc (z 2) := hZ 2
  have key : ∀ n < 27, A n = enc (z 0 ^ (n / 9) * z 1 ^ (n / 3 % 3) * z 2 ^ (n % 3)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      cases n with
      | zero =>
        simp only [Nat.zero_div, Nat.zero_mod, pow_zero, mul_one]
        rw [henc.enc_one]
        exact Nat.eq_of_beq_eq_true h0
      | succ i =>
        have e := hst i (by omega)
        unfold aStep at e
        cases hb : Nat.beq (Nat.mod (Nat.succ i) 3) 0 with
        | false =>
          rw [hb] at e
          have h1 : (i + 1) % 3 ≠ 0 := Nat.ne_of_beq_eq_false hb
          have e' : Nat.beq (A (i + 1)) (MULF (A i) (Z 2)) = true := e
          rw [Nat.eq_of_beq_eq_true e', ih i (by omega) (by omega), hZ2, ← henc.enc_mul]
          have ea : (i + 1) / 9 = i / 9 := by omega
          have eb : (i + 1) / 3 % 3 = i / 3 % 3 := by omega
          have ec : (i + 1) % 3 = i % 3 + 1 := by omega
          rw [ea, eb, ec, pow_succ, ← mul_assoc]
        | true =>
          rw [hb] at e
          have h1 : (i + 1) % 3 = 0 := Nat.eq_of_beq_eq_true hb
          cases hb2 : Nat.beq (Nat.mod (Nat.div (Nat.succ i) 3) 3) 0 with
          | false =>
            rw [hb2] at e
            have h2 : (i + 1) / 3 % 3 ≠ 0 := Nat.ne_of_beq_eq_false hb2
            have e' : Nat.beq (A (i + 1)) (MULF (A (i + 1 - 3)) (Z 1)) = true := e
            rw [Nat.eq_of_beq_eq_true e', ih (i + 1 - 3) (by omega) (by omega), hZ1,
              ← henc.enc_mul]
            have ea : (i + 1) / 9 = (i + 1 - 3) / 9 := by omega
            have eb : (i + 1) / 3 % 3 = (i + 1 - 3) / 3 % 3 + 1 := by omega
            have ec : (i + 1 - 3) % 3 = 0 := by omega
            rw [h1, ea, eb, ec, pow_succ]
            simp only [pow_zero, mul_one, mul_assoc]
          | true =>
            rw [hb2] at e
            have h2 : (i + 1) / 3 % 3 = 0 := Nat.eq_of_beq_eq_true hb2
            have e' : Nat.beq (A (i + 1)) (MULF (A (i + 1 - 9)) (Z 0)) = true := e
            rw [Nat.eq_of_beq_eq_true e', ih (i + 1 - 9) (by omega) (by omega), hZ0,
              ← henc.enc_mul]
            have ea : (i + 1) / 9 = (i + 1 - 9) / 9 + 1 := by omega
            have eb : (i + 1 - 9) / 3 % 3 = 0 := by omega
            have ec : (i + 1 - 9) % 3 = 0 := by omega
            rw [h1, h2, ea, eb, ec, pow_succ]
            simp only [pow_zero, mul_one]
  intro a ha b hb c hc
  have e := key (9 * a + 3 * b + c) (by omega)
  have e1 : (9 * a + 3 * b + c) / 9 = a := by omega
  have e2 : (9 * a + 3 * b + c) / 3 % 3 = b := by omega
  have e3 : (9 * a + 3 * b + c) % 3 = c := by omega
  rwa [e1, e2, e3] at e

theorem aAdd_sound {A : Nat → Nat} (h : aAddK A = true) :
    ∀ i < 27, ∀ m < 27, MULF (A i) (A m) = A (addIdx i m) := by
  intro i hi m hm
  have e := allBelow_sound (by decide) h (27 * i + m) (by omega)
  have e1 : (27 * i + m) / 27 = i := by omega
  have e2 : (27 * i + m) % 27 = m := by omega
  have e' : Nat.beq (MULF (A ((27 * i + m) / 27)) (A ((27 * i + m) % 27)))
      (A (addIdx ((27 * i + m) / 27) ((27 * i + m) % 27))) = true := e
  rw [e1, e2] at e'
  exact Nat.eq_of_beq_eq_true e'

theorem wK_sound {WG WX WP WC : Nat → Nat} (h : wK WG WX WP WC = true) :
    WX 0 = ONE ∧
      (∀ i < 47, Nat.land (WP i) 255 ≤ i ∧ Nat.shiftRight (WP i) 8 < 3 ∧
        WX (i + 1) = MULF (WX (Nat.land (WP i) 255)) (WG (Nat.shiftRight (WP i) 8))) ∧
      ∀ i < 144, WC i < 48 ∧ WX (WC i) = MULF (WX (i / 3)) (WG (i % 3)) := by
  simp only [wK, Bool.and_eq_true] at h
  obtain ⟨⟨h0, hb⟩, hc⟩ := h
  unfold buildG at hb
  have h47 : Nat.sub 48 1 = 47 := rfl
  rw [h47] at hb
  refine ⟨Nat.eq_of_beq_eq_true h0, fun i hi => ?_, fun i hi => ?_⟩
  · have e := allBelow_sound (by decide) hb i hi
    simp only [Bool.and_eq_true] at e
    exact ⟨Nat.le_of_ble_eq_true e.1.1, Nat.blt_eq.mp e.1.2, Nat.eq_of_beq_eq_true e.2⟩
  · have e := allBelow_sound (by decide) hc i hi
    simp only [Bool.and_eq_true] at e
    exact ⟨Nat.blt_eq.mp e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem wm_sound {Z A WX WM : Nat → Nat} (h : wmK Z A WX WM = true) :
    ∀ p < 144, WM p < 27 ∧ MULF (WX (p / 3)) (Z (p % 3)) = MULF (A (WM p)) (WX (p / 3)) := by
  intro p hp
  have e := allBelow_sound (by decide) h p hp
  simp only [Bool.and_eq_true] at e
  exact ⟨Nat.blt_eq.mp e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem frame_sound {Z A WX FR : Nat → Nat} (h : frameK Z A WX FR = true) :
    ∀ t < 216, distH (t / 36) (t / 6 % 6) (t % 6) = true → FR t < 1296 ∧
      frameAt Z (elt A WX (FR t)) (t / 36) (t / 6 % 6) (t % 6) = true := by
  intro t ht hd
  have e := allBelow_sound (by decide) h t ht
  have e' : (!(distH (t / 36) (t / 6 % 6) (t % 6)) || (Nat.blt (FR t) 1296 &&
      frameAt Z (elt A WX (FR t)) (t / 36) (t / 6 % 6) (t % 6))) = true := e
  rw [hd, Bool.not_true, Bool.false_or, Bool.and_eq_true] at e'
  exact ⟨Nat.blt_eq.mp e'.1, e'.2⟩

private theorem bits_step {S : Nat → Nat} (P : Nat → Bool) (h0 : S 0 = 0)
    (hs : ∀ L, S (L + 1) = cond (P L) (2 ^ L) 0 + S L) :
    ∀ L, S L < 2 ^ L ∧ ∀ y, (S L).testBit y = (decide (y < L) && P y) := by
  intro L
  induction L with
  | zero => exact ⟨by rw [h0]; exact Nat.one_pos, fun y => by rw [h0, Nat.zero_testBit]; simp⟩
  | succ L ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [hs L]
    cases hP : P L
    · refine ⟨by rw [cond_false, Nat.zero_add, Nat.pow_succ]; omega, fun y => ?_⟩
      rw [cond_false, Nat.zero_add, h2]
      rcases Nat.lt_trichotomy y L with hy | rfl | hy
      · simp [hy, Nat.lt_succ_of_lt hy]
      · simp [hP]
      · have a : ¬ y < L := by omega
        have b : ¬ y < L + 1 := by omega
        simp [a, b]
    · refine ⟨by rw [cond_true, Nat.pow_succ]; omega, fun y => ?_⟩
      rw [cond_true]
      rcases Nat.lt_trichotomy y L with hy | rfl | hy
      · rw [Nat.testBit_two_pow_add_gt hy, h2]
        simp [hy, Nat.lt_succ_of_lt hy]
      · rw [Nat.testBit_two_pow_add_eq, h2]
        simp [hP]
      · have b : ¬ y < L + 1 := by omega
        have hlt : 2 ^ L + S L < 2 ^ y :=
          lt_of_lt_of_le (by rw [Nat.pow_succ]; omega) (Nat.pow_le_pow_right (by decide) hy)
        rw [Nat.testBit_lt_two_pow hlt]
        simp [b]

private theorem bits_rec (f : Nat → Nat) (P : Nat → Bool) (hf : ∀ l, f l = cond (P l) (2 ^ l) 0)
    (L : Nat) : ∀ y, (Nat.rec (motive := fun _ => Nat) 0 (fun l acc => Nat.add (f l) acc) L).testBit y =
      (decide (y < L) && P y) :=
  (bits_step (S := fun L => Nat.rec (motive := fun _ => Nat) 0 (fun l acc => Nat.add (f l) acc) L) P
    rfl (fun L => by rw [← hf L]; rfl) L).2

private theorem cmask_testBit (A : Nat → Nat) (s : Nat) {y : Nat} (hy : y < 27) :
    (cmask A s).testBit y = commB s (A y) := by
  have hg : ∀ l, (fun i => Bool.rec (motive := fun _ => Nat) 0
      (cond (commB s (A i)) (Nat.shiftLeft 1 i) 0) (Nat.blt i 27)) (Nat.add (Nat.shiftLeft 0 6) l) =
      cond (decide (l < 27) && commB s (A l)) (2 ^ l) 0 := by
    intro l
    have e0 : Nat.add (Nat.shiftLeft 0 6) l = l := by
      change 0 <<< 6 + l = l
      rw [Nat.zero_shiftLeft, Nat.zero_add]
    have e1 : Nat.shiftLeft 1 l = 2 ^ l := Nat.one_shiftLeft l
    simp only [e0, e1]
    by_cases hl : l < 27
    · rw [Nat.blt_eq.mpr hl]
      simp [hl]
    · have hb : Nat.blt l 27 = false := by
        cases hb : Nat.blt l 27 with
        | false => rfl
        | true => exact absurd (Nat.blt_eq.mp hb) hl
      rw [hb]
      simp [hl]
  have hb := bits_rec _ _ hg 64 y
  have h64 : y < 64 := by omega
  have e : cmask A s = Nat.add (Nat.rec (motive := fun _ => Nat) 0 (fun l acc => Nat.add
      ((fun i => Bool.rec (motive := fun _ => Nat) 0 (cond (commB s (A i)) (Nat.shiftLeft 1 i) 0)
        (Nat.blt i 27)) (Nat.add (Nat.shiftLeft 0 6) l)) acc) 64) 0 := rfl
  rw [e, Nat.add_eq, Nat.add_zero, hb]
  simp [hy, h64]

theorem look_sound {A WX QI RT RS RI RW : Nat → Nat} (h : lookK A WX QI RT RS RI RW = true) :
    ∀ n < 1296, MULF (elt A WX n) (elt A WX n) = ONE → elt A WX n ≠ ONE →
      ∀ x < 27, x ≠ 0 → commB (elt A WX n) (A x) = true →
        (∃ y < 27, y ≠ 0 ∧ y ≠ x ∧ y ≠ addIdx x x ∧ commB (elt A WX n) (A y) = true) →
          recAt A WX RS RI RW (elt A WX n) x (RT (27 * QI n + x)) = true := by
  intro n hn hsq hne x hx hx0 hcx hy
  obtain ⟨y, hy27, hy0, hyx, hyax, hcy⟩ := hy
  have e := allBelow_sound (by decide) h n hn
  simp only [strictB_eq] at e
  have b1 : Nat.beq (MULF (elt A WX n) (elt A WX n)) ONE = true := by
    rw [Nat.beq_eq]
    exact hsq
  have b2 : Nat.beq (elt A WX n) ONE = false := by
    cases hb : Nat.beq (elt A WX n) ONE with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) hne
  simp only [b1, b2, Bool.not_false, Bool.not_true, Bool.true_and, Bool.and_true, Bool.false_or,
    Bool.and_eq_true] at e
  have e2 := allBelow_sound (by decide) e.2 x hx
  have bx : Nat.beq x 0 = false := by
    cases hb : Nat.beq x 0 with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) hx0
  have tx : Nat.testBit (cmask A (elt A WX n)) x = true := by
    rw [cmask_testBit A _ hx, hcx]
  have hl : Nat.testBit (lineMask x) y = false := by
    have e3 : lineMask x = (1 ||| 1 <<< x) ||| 1 <<< addIdx x x := rfl
    have h1y : Nat.testBit 1 y = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hy0)
    rw [e3, Nat.testBit_or, Nat.testBit_or, Nat.one_shiftLeft, Nat.one_shiftLeft,
      Nat.testBit_two_pow, Nat.testBit_two_pow, h1y]
    simp [Ne.symm hyx, Ne.symm hyax]
  have bl : Nat.beq (Nat.land (cmask A (elt A WX n)) (Nat.xor (lineMask x) 134217727)) 0 = false := by
    cases hb : Nat.beq (Nat.land (cmask A (elt A WX n)) (Nat.xor (lineMask x) 134217727)) 0 with
    | false => rfl
    | true =>
      have h0 := congrArg (fun v => Nat.testBit v y) (Nat.eq_of_beq_eq_true hb)
      change Nat.testBit (cmask A (elt A WX n) &&& (lineMask x ^^^ 134217727)) y =
        Nat.testBit 0 y at h0
      have h27 : Nat.testBit 134217727 y = true := by
        have e4 : (134217727 : Nat) = 2 ^ 27 - 1 := by decide
        rw [e4, Nat.testBit_two_pow_sub_one]
        simp [hy27]
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, cmask_testBit A _ hy27, hcy, hl,
        h27] at h0
      simp at h0
  simp only [bx, tx, bl, Bool.false_or, Bool.not_true] at e2
  exact e2

theorem c7_sound {CG CX CP CS : Nat → Nat} {w : Nat} (h : c7K CG CX CP CS w = true) :
    commB (CG 0) w = true ∧ commB (CG 1) w = true ∧
      (∀ k < 648, treeAt MULF ONE CG 2 CX CP k = true) ∧ ∀ i < 648, sortAt 648 CX CS i = true := by
  simp only [c7K, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, allBelow_sound (by decide) h.1.2, allBelow_sound (by decide) h.2⟩

theorem orb_sound {HG HI OX OP OS : Nat → Nat} {w : Nat} (h : orbK HG HI OX OP OS w = true) :
    MULF (HG 0) (HI 0) = ONE ∧ MULF (HG 1) (HI 1) = ONE ∧
      (∀ k < 2240, treeAt (conjH HG HI) w (fun l => l) 2 OX OP k = true) ∧
      ∀ i < 2240, sortAt 2240 OX OS i = true := by
  simp only [orbK, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.1, Nat.eq_of_beq_eq_true h.1.1.2,
    allBelow_sound (by decide) h.1.2, allBelow_sound (by decide) h.2⟩

theorem rTab_sound {RG RX RP RC : Nat → Nat} {nG nR s l : Nat} (hm : nR ≤ 64)
    (h : rTabK RG RX RP RC nG nR s l = true) :
    (∀ k < nR, treeAt MULF ONE RG nG RX RP k = true) ∧
      (∀ k < nR, closedAt MULF RG nG nR RX RC k = true) ∧
      (∀ i < nR, sortAt nR RX (fun i => RC (Nat.add (Nat.mul nR nG) i)) i = true) ∧
      ∀ i < nR, commB (RX i) s = true ∧ commB (RX i) l = true := by
  simp only [rTabK, Bool.and_eq_true] at h
  have hm' : nR ≤ 64 * 1 := by omega
  refine ⟨allBelow_sound hm' h.1.1.1, allBelow_sound hm' h.1.1.2, allBelow_sound hm' h.1.2,
    fun i hi => ?_⟩
  have e := allBelow_sound hm' h.2 i hi
  rw [Bool.and_eq_true] at e
  exact e

theorem rep_sound {TX RG RX RR : Nat → Nat} {n hi nG nR s : Nat} (hm : n ≤ 64 * hi)
    (h : repK TX RG RX RR n hi nG nR s = true) :
    ∀ p < n, commB (TX p) s = true → repRec TX RG RX n nG nR s (TX p) (RR p) = true := by
  intro p hp hc
  have e := allBelow_sound hm h p hp
  rw [strictB_eq, hc, Bool.not_true, Bool.false_or] at e
  exact e

theorem repRec_sound {TX RG RX : Nat → Nat} {n nG nR s x r : Nat} (hG : nG ≤ 64)
    (h : repRec TX RG RX n nG nR s x r = true) :
    (∀ g < nG, ∃ j < nR, MULF (RX j) x = MULF x (RG g)) ∧
      ((∃ j < nR, RX j = x) ∨ P2K x 9 ≠ ONE ∨
        ∃ a < n, ∃ b < n, MULF (TX a) (TX b) = ONE ∧ commB (TX a) s = true ∧
          P2K (MULF x (MULF (MULF (TX a) x) (TX b))) 9 ≠ ONE) := by
  simp only [repRec, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun g hg => ?_, ?_⟩
  · have e := allBelow_sound (by omega) h1 g hg
    simp only [Bool.and_eq_true] at e
    exact ⟨_, Nat.blt_eq.mp e.1, Nat.eq_of_beq_eq_true e.2⟩
  · rcases h2 with (⟨ha, hb⟩ | hp) | ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩
    · exact Or.inl ⟨_, Nat.blt_eq.mp ha, Nat.eq_of_beq_eq_true hb⟩
    · exact Or.inr (Or.inl (Nat.ne_of_beq_eq_false hp))
    · exact Or.inr (Or.inr ⟨_, Nat.blt_eq.mp ha, _, Nat.blt_eq.mp hb, Nat.eq_of_beq_eq_true hc, hd,
        Nat.ne_of_beq_eq_false he⟩)

theorem ab_sound {RX : Nat → Nat} {nR : Nat} (hm : nR * nR ≤ 64) (h : abK RX nR = true) :
    (∀ i < nR, ∀ j < nR, commB (RX i) (RX j) = true) ∧ ∀ i < nR, MULF (RX i) (RX i) = ONE := by
  simp only [abK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hR : nR ≤ 64 * 1 := by
    have := Nat.le_mul_self nR
    omega
  refine ⟨fun i hi j hj => ?_, fun i hi => Nat.eq_of_beq_eq_true (allBelow_sound hR h2 i hi)⟩
  have hpos : 0 < nR := by omega
  have hp : nR * i + j < nR * nR := by
    have := Nat.mul_le_mul_left nR (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at this
    omega
  have hm' : Nat.mul nR nR ≤ 64 * 1 := by
    change nR * nR ≤ 64 * 1
    omega
  have e := allBelow_sound hm' h1 (nR * i + j) hp
  have e1 : (nR * i + j) / nR = i := by rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hj, Nat.add_zero]
  have e2 : (nR * i + j) % nR = j := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have e' : commB (RX ((nR * i + j) / nR)) (RX ((nR * i + j) % nR)) = true := e
  rwa [e1, e2] at e'

theorem sl_sound {HG HI : Nat → Nat} {n v w t : Nat} (h : slK HG HI n v w t = true) :
    MULF (wordH HG HI n v) w = MULF t (wordH HG HI n v) := by
  rw [slK, strictB_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem sortK_sound {X SRT SRI : Nat → Nat} {n hi : Nat} (hm : n ≤ 64 * hi)
    (h : CFSG.KD.G2Three.sortK X SRT SRI n hi = true) :
    (∀ p < n, SRT p < n) ∧ ∀ t < n, ∃ p < n, SRT p = t := by
  have e := allBelow_sound hm h
  refine ⟨fun p hp => ?_, fun t ht => ?_⟩
  · have ep := e p hp
    simp only [Bool.and_eq_true] at ep
    exact Nat.blt_eq.mp ep.1.1.1.1
  · have et := e t ht
    simp only [Bool.and_eq_true] at et
    exact ⟨_, Nat.blt_eq.mp et.1.1.1.2, Nat.eq_of_beq_eq_true et.1.2⟩

end CFSG.KC.Misc.Sp6RefS

end
