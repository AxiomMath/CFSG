module

public import Certificates.Data.Kernel.Spor.ONK
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.ONLane

@[expose] def laneOf (k N : Nat) : Nat := (N >>> (256 * k)) % 2 ^ 256

theorem testBit_laneOf (k N i : Nat) :
    (laneOf k N).testBit i = (decide (i < 256) && N.testBit (256 * k + i)) := by
  unfold laneOf
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem laneOf_lt (k N : Nat) : laneOf k N < 2 ^ 256 := Nat.mod_lt _ (Nat.two_pow_pos 256)

theorem laneOf_lor (k a b : Nat) : laneOf k (Nat.lor a b) = Nat.lor (laneOf k a) (laneOf k b) :=
  Nat.eq_of_testBit_eq fun i => by
    change (laneOf k (a ||| b)).testBit i = (laneOf k a ||| laneOf k b).testBit i
    simp only [testBit_laneOf, Nat.testBit_or]
    cases decide (i < 256) <;> simp

theorem laneOf_land (k a b : Nat) : laneOf k (Nat.land a b) = Nat.land (laneOf k a) (laneOf k b) :=
  Nat.eq_of_testBit_eq fun i => by
    change (laneOf k (a &&& b)).testBit i = (laneOf k a &&& laneOf k b).testBit i
    simp only [testBit_laneOf, Nat.testBit_and]
    cases decide (i < 256) <;> simp

theorem laneOf_xor (k a b : Nat) : laneOf k (Nat.xor a b) = Nat.xor (laneOf k a) (laneOf k b) :=
  Nat.eq_of_testBit_eq fun i => by
    change (laneOf k (a ^^^ b)).testBit i = (laneOf k a ^^^ laneOf k b).testBit i
    simp only [testBit_laneOf, Nat.testBit_xor]
    cases decide (i < 256) <;> simp

private theorem tb_false {x i w : Nat} (hx : x < 2 ^ w) (hw : w ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hw))

theorem laneOf_add_mul {k n a b : Nat} (ha : a < 2 ^ (256 * n)) (hb : b < 2 ^ 256) :
    laneOf k (2 ^ (256 * n) * b + a) = if k = n then b else if k < n then laneOf k a else 0 := by
  rw [Nat.two_pow_add_eq_or_of_lt ha]
  rcases Nat.lt_trichotomy k n with h | h | h
  · have h0 : k ≠ n := by omega
    simp only [h0, h, ↓reduceIte]
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp only [testBit_laneOf, Nat.testBit_or, Nat.testBit_two_pow_mul]
    by_cases hi : i < 256
    · have : ¬ 256 * k + i ≥ 256 * n := by omega
      simp [hi, this]
    · simp [hi]
  · subst h
    simp only [↓reduceIte]
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp only [testBit_laneOf, Nat.testBit_or, Nat.testBit_two_pow_mul]
    by_cases hi : i < 256
    · have h1 : a.testBit (256 * k + i) = false := tb_false ha (by omega)
      simp [hi, h1]
    · have h1 : b.testBit i = false := tb_false hb (by omega)
      simp [hi, h1]
  · have h0 : k ≠ n := by omega
    have h3 : ¬ k < n := by omega
    simp only [h0, h3, ↓reduceIte]
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp only [testBit_laneOf, Nat.testBit_or, Nat.testBit_two_pow_mul, Nat.zero_testBit]
    by_cases hi : i < 256
    · have h1 : a.testBit (256 * k + i) = false := tb_false ha (by omega)
      have h2 : b.testBit (256 * k + i - 256 * n) = false := tb_false hb (by omega)
      simp [hi, h1, h2]
    · simp [hi]

theorem laneOf_zero (k : Nat) : laneOf k 0 = 0 := by simp [laneOf]

theorem laneOf_mul : ∀ (n : Nat) {s c : Nat}, c < 2 ^ 256 → s < 2 ^ (256 * n) →
    (∀ i, s.testBit i = true → i % 256 = 0) →
    c * s < 2 ^ (256 * n) ∧ ∀ k, laneOf k (c * s) = if s.testBit (256 * k) = true then c else 0
  | 0, s, c, _, hs, _ => by
    have : s = 0 := by simpa using hs
    subst this
    simp [laneOf_zero]
  | n + 1, s, c, hc, hs, hbits => by
    have hpos : 0 < 2 ^ (256 * n) := Nat.two_pow_pos _
    have hsplit : s = 2 ^ (256 * n) * (s / 2 ^ (256 * n)) + s % 2 ^ (256 * n) :=
      (Nat.div_add_mod s _).symm
    have hb2 : ∀ i, (s / 2 ^ (256 * n)).testBit i = s.testBit (256 * n + i) := fun i => by
      rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    have hlt : s / 2 ^ (256 * n) < 2 ^ 256 := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add]
      exact Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega))
    have hb1 : s / 2 ^ (256 * n) ≤ 1 := by
      have hz : (s / 2 ^ (256 * n)) >>> 1 = 0 := Nat.eq_of_testBit_eq fun i => by
        rw [Nat.testBit_shiftRight, Nat.zero_testBit]
        by_cases hi : 1 + i < 256
        · cases h : (s / 2 ^ (256 * n)).testBit (1 + i)
          · rfl
          · have := hbits _ ((hb2 _).symm.trans h)
            omega
        · exact tb_false hlt (by omega)
      rw [Nat.shiftRight_eq_div_pow] at hz
      omega
    have hs' : s % 2 ^ (256 * n) < 2 ^ (256 * n) := Nat.mod_lt _ hpos
    have hbits' : ∀ i, (s % 2 ^ (256 * n)).testBit i = true → i % 256 = 0 := fun i h => by
      rw [Nat.testBit_mod_two_pow, Bool.and_eq_true] at h
      exact hbits i h.2
    obtain ⟨ih1, ih2⟩ := laneOf_mul n hc hs' hbits'
    have hb0 : s.testBit (256 * n) = decide (s / 2 ^ (256 * n) = 1) := by
      have := hb2 0
      rw [Nat.add_zero] at this
      rw [← this]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with h | h <;> rw [h] <;> rfl
    generalize s / 2 ^ (256 * n) = b at hsplit hb1 hb0
    generalize s % 2 ^ (256 * n) = s' at hsplit hs' hbits' ih1 ih2
    have hcb : c * b < 2 ^ 256 := Nat.lt_of_le_of_lt (by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with h | h <;> simp [h]) hc
    have he : c * s = 2 ^ (256 * n) * (c * b) + c * s' := by
      rw [hsplit, Nat.mul_add, Nat.mul_left_comm]
    refine ⟨?_, fun k => ?_⟩
    · rw [he, Nat.mul_add 256 n 1, Nat.pow_add]
      have : 2 ^ (256 * n) * (c * b) + 2 ^ (256 * n) ≤ 2 ^ (256 * n) * 2 ^ (256 * 1) := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ hcb
      omega
    · rw [he, laneOf_add_mul ih1 hcb]
      rcases Nat.lt_trichotomy k n with h | h | h
      · have h0 : k ≠ n := by omega
        have e : s.testBit (256 * k) = s'.testBit (256 * k) := by
          rw [hsplit, Nat.two_pow_add_eq_or_of_lt hs', Nat.testBit_or, Nat.testBit_two_pow_mul]
          have : ¬ 256 * k ≥ 256 * n := by omega
          simp [this]
        simp only [h0, h, ↓reduceIte, ih2 k, e]
      · subst h
        simp only [↓reduceIte, hb0]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with h | h <;> simp [h]
      · have h0 : k ≠ n := by omega
        have h3 : ¬ k < n := by omega
        have e : s.testBit (256 * k) = false := tb_false hs (by omega)
        simp only [h0, h3, ↓reduceIte, e]
        rfl

@[expose] def oneL (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => Nat.lor ih (Nat.shiftLeft 1 (Nat.mul 256 k))) n

theorem testBit_oneL : ∀ (n i : Nat), (oneL n).testBit i = decide (i % 256 = 0 ∧ i < 256 * n)
  | 0, i => by
    change (0 : Nat).testBit i = decide (i % 256 = 0 ∧ i < 256 * 0)
    simp
  | n + 1, i => by
    change (oneL n ||| 1 <<< (256 * n)).testBit i = _
    rw [Nat.testBit_or, testBit_oneL n i, Nat.testBit_shiftLeft]
    have : (1 : Nat).testBit (i - 256 * n) = decide (i - 256 * n = 0) := by
      cases i - 256 * n <;> simp [Nat.testBit_succ]
    rw [this]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

theorem sel_spec (n t x : Nat) :
    Nat.land (x >>> t) (oneL n) < 2 ^ (256 * n) ∧
    (∀ i, (Nat.land (x >>> t) (oneL n)).testBit i = true → i % 256 = 0) ∧
    ∀ k, (Nat.land (x >>> t) (oneL n)).testBit (256 * k) = (decide (k < n) && x.testBit (t + 256 * k)) := by
  have hb : ∀ i, (Nat.land (x >>> t) (oneL n)).testBit i =
      (x.testBit (t + i) && decide (i % 256 = 0 ∧ i < 256 * n)) := fun i => by
    change ((x >>> t) &&& oneL n).testBit i = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_oneL]
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, fun i h => ?_, fun k => ?_⟩
  · rw [hb]
    have : ¬ (i % 256 = 0 ∧ i < 256 * n) := by omega
    simp [this]
  · rw [hb] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.1
  · rw [hb]
    have e : (256 * k % 256 = 0 ∧ 256 * k < 256 * n) ↔ k < n := by omega
    simp only [e, Bool.and_comm]

open CFSG.KC.Enum CFSG.KS.ON

@[expose] noncomputable def mvLW (n o : Nat) (L : List Nat) : Nat → Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat)
    (fun _ _ _ ap am => Nat.lor ap (Nat.shiftLeft am (Nat.mul 256 n)))
    (fun c _ ih t xp xm ap am =>
      strictN (vP c) fun cp => strictN (vM c) fun cm =>
      strictN (Nat.land (Nat.shiftRight xp t) o) fun sp =>
      strictN (Nat.land (Nat.shiftRight xm t) o) fun sm =>
      strictN (Nat.lor (Nat.mul cp sp) (Nat.mul cm sm)) fun bp =>
      strictN (Nat.lor (Nat.mul cm sp) (Nat.mul cp sm)) fun bm =>
      strictN (addP ap am bp bm) fun ap' => strictN (addM ap am bp bm) fun am' =>
        ih (Nat.succ t) xp xm ap' am')
    L

theorem laneOf_addP (k ap am bp bm : Nat) :
    laneOf k (addP ap am bp bm) = addP (laneOf k ap) (laneOf k am) (laneOf k bp) (laneOf k bm) := by
  simp only [addP, laneOf_lor, laneOf_land, laneOf_xor]

theorem laneOf_addM (k ap am bp bm : Nat) :
    laneOf k (addM ap am bp bm) = addM (laneOf k ap) (laneOf k am) (laneOf k bp) (laneOf k bm) := by
  simp only [addM, laneOf_lor, laneOf_land, laneOf_xor]

theorem addP_zero (a m : Nat) : addP a m 0 0 = a := by
  change (a ^^^ (a &&& (0 ||| 0))) ||| (0 ^^^ (0 &&& (a ||| m))) ||| (m &&& 0) = a
  simp

theorem addM_zero (a m : Nat) : addM a m 0 0 = m := by
  change (m ^^^ (m &&& (0 ||| 0))) ||| (0 ^^^ (0 &&& (a ||| m))) ||| (a &&& 0) = m
  simp

private theorem nIfE (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem land_one_beq (y : Nat) : Nat.beq (Nat.land y 1) 1 = y.testBit 0 := by
  change Nat.beq (y &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one y with h | h <;> rw [h] <;> rfl

private theorem mvL_cons' (c : Nat) (L : List Nat) (xp xm ap am : Nat) : mvL (c :: L) xp xm ap am =
    if xp.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vP c) (vM c)) (addM ap am (vP c) (vM c))
    else if xm.testBit 0 = true then
      mvL L (xp >>> 1) (xm >>> 1) (addP ap am (vM c) (vP c)) (addM ap am (vM c) (vP c))
    else mvL L (xp >>> 1) (xm >>> 1) ap am := by
  have e : mvL (c :: L) xp xm ap am = strictN (vP c) fun cp => strictN (vM c) fun cm =>
      nIf(Nat.beq (Nat.land xp (nat_lit 1)) (nat_lit 1),
        strictN (addP ap am cp cm) fun ap' => strictN (addM ap am cp cm) fun am' =>
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
        nIf(Nat.beq (Nat.land xm (nat_lit 1)) (nat_lit 1),
          strictN (addP ap am cm cp) fun ap' => strictN (addM ap am cm cp) fun am' =>
            mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap' am',
          mvL L (Nat.shiftRight xp (nat_lit 1)) (Nat.shiftRight xm (nat_lit 1)) ap am)) := rfl
  rw [e]
  simp only [PackFld.strictN_eqP, nIfE, land_one_beq]
  rfl

private theorem bitwise_lt {w : Nat} {a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    Nat.lor a b < 2 ^ w ∧ Nat.land a b < 2 ^ w ∧ Nat.xor a b < 2 ^ w :=
  ⟨Nat.or_lt_two_pow ha hb, Nat.and_lt_two_pow a hb, Nat.xor_lt_two_pow ha hb⟩

theorem addP_lt {w ap am bp bm : Nat} (h1 : ap < 2 ^ w) (h2 : am < 2 ^ w) (h3 : bp < 2 ^ w)
    (h4 : bm < 2 ^ w) : addP ap am bp bm < 2 ^ w ∧ addM ap am bp bm < 2 ^ w := by
  have l := @bitwise_lt w
  constructor
  · exact (l (l (l h1 (l h1 (l h3 h4).1).2.1).2.2 (l h3 (l h3 (l h1 h2).1).2.1).2.2).1
      (l h2 h4).2.1).1
  · exact (l (l (l h2 (l h2 (l h3 h4).1).2.1).2.2 (l h4 (l h4 (l h1 h2).1).2.1).2.2).1
      (l h1 h3).2.1).1

private theorem vP_lt (c : Nat) : vP c < 2 ^ 256 :=
  Nat.and_lt_two_pow c (by decide : mask (nat_lit 256) < 2 ^ 256)

private theorem mvLW_cons (n o c : Nat) (L : List Nat) (t xp xm ap am : Nat) :
    mvLW n o (c :: L) t xp xm ap am = mvLW n o L (t + 1) xp xm
      (addP ap am (Nat.lor (vP c * Nat.land (xp >>> t) o) (vM c * Nat.land (xm >>> t) o))
        (Nat.lor (vM c * Nat.land (xp >>> t) o) (vP c * Nat.land (xm >>> t) o)))
      (addM ap am (Nat.lor (vP c * Nat.land (xp >>> t) o) (vM c * Nat.land (xm >>> t) o))
        (Nat.lor (vM c * Nat.land (xp >>> t) o) (vP c * Nat.land (xm >>> t) o))) := by
  change (strictN (vP c) fun cp => strictN (vM c) fun cm =>
      strictN (Nat.land (Nat.shiftRight xp t) o) fun sp =>
      strictN (Nat.land (Nat.shiftRight xm t) o) fun sm =>
      strictN (Nat.lor (Nat.mul cp sp) (Nat.mul cm sm)) fun bp =>
      strictN (Nat.lor (Nat.mul cm sp) (Nat.mul cp sm)) fun bm =>
      strictN (addP ap am bp bm) fun ap' => strictN (addM ap am bp bm) fun am' =>
        mvLW n o L (Nat.succ t) xp xm ap' am') = _
  simp only [PackFld.strictN_eqP]
  rfl

theorem mvLW_spec (n : Nat) : ∀ (L : List Nat) (t xp xm ap am : Nat),
    t + L.length ≤ 256 → Nat.land xp xm = 0 → (∀ c ∈ L, vM c < 2 ^ 256) →
    ap < 2 ^ (256 * n) → am < 2 ^ (256 * n) →
    ∃ P M, mvLW n (oneL n) L t xp xm ap am = Nat.lor P (Nat.shiftLeft M (Nat.mul 256 n)) ∧
      P < 2 ^ (256 * n) ∧ ∀ k < n, mvL L (laneOf k xp >>> t) (laneOf k xm >>> t) (laneOf k ap)
        (laneOf k am) = vmk (laneOf k P) (laneOf k M)
  | [], _, _, _, ap, am, _, _, _, hap, _ => ⟨ap, am, rfl, hap, fun _ _ => rfl⟩
  | c :: L, t, xp, xm, ap, am, ht, hd, hc, hap, ham => by
    have hcm : vM c < 2 ^ 256 := hc c List.mem_cons_self
    obtain ⟨hsp1, hsp2, hsp3⟩ := sel_spec n t xp
    obtain ⟨hsm1, hsm2, hsm3⟩ := sel_spec n t xm
    have m1 := laneOf_mul n (vP_lt c) hsp1 hsp2
    have m2 := laneOf_mul n hcm hsm1 hsm2
    have m3 := laneOf_mul n hcm hsp1 hsp2
    have m4 := laneOf_mul n (vP_lt c) hsm1 hsm2
    have hbp := Nat.or_lt_two_pow m1.1 m2.1
    have hbm := Nat.or_lt_two_pow m3.1 m4.1
    obtain ⟨hap', ham'⟩ := addP_lt hap ham hbp hbm
    have ht' : (t + 1) + L.length ≤ 256 := by simp only [List.length_cons] at ht; omega
    obtain ⟨P, M, he, hP, hl⟩ := mvLW_spec n L (t + 1) xp xm _ _ ht' hd
      (fun c' h => hc c' (List.mem_cons_of_mem _ h)) hap' ham'
    refine ⟨P, M, (mvLW_cons ..).trans he, hP, fun k hk => ?_⟩
    have hor : ∀ a b, laneOf k (a ||| b) = laneOf k a ||| laneOf k b := laneOf_lor k
    rw [← hl k hk, mvL_cons', laneOf_addP, laneOf_addM, hor, hor, m1.2, m2.2, m3.2,
      m4.2, hsp3, hsm3, ← Nat.shiftRight_add, ← Nat.shiftRight_add]
    have hx : (laneOf k xp >>> t).testBit 0 = xp.testBit (t + 256 * k) := by
      rw [Nat.testBit_shiftRight, testBit_laneOf, Nat.add_zero, Nat.add_comm (256 * k)]
      simp only [show t < 256 by simp only [List.length_cons] at ht; omega, decide_true,
        Bool.true_and]
    have hy : (laneOf k xm >>> t).testBit 0 = xm.testBit (t + 256 * k) := by
      rw [Nat.testBit_shiftRight, testBit_laneOf, Nat.add_zero, Nat.add_comm (256 * k)]
      simp only [show t < 256 by simp only [List.length_cons] at ht; omega, decide_true,
        Bool.true_and]
    have hxy : ¬ (xp.testBit (t + 256 * k) = true ∧ xm.testBit (t + 256 * k) = true) := by
      intro ⟨h1, h2⟩
      have : (Nat.land xp xm).testBit (t + 256 * k) = true := by
        change (xp &&& xm).testBit _ = true
        rw [Nat.testBit_and, h1, h2]
        rfl
      rw [hd, Nat.zero_testBit] at this
      exact Bool.false_ne_true this
    rw [hx, hy]
    simp only [hk, decide_true, Bool.true_and]
    cases h1 : xp.testBit (t + 256 * k) <;> cases h2 : xm.testBit (t + 256 * k)
    · simp only [↓reduceIte, Bool.false_eq_true]
      change _ = mvL L _ _ (addP _ _ (0 ||| 0) (0 ||| 0)) (addM _ _ (0 ||| 0) (0 ||| 0))
      rw [Nat.or_self, addP_zero, addM_zero]
    · simp only [↓reduceIte, Bool.false_eq_true]
      change _ = mvL L _ _ (addP _ _ (0 ||| vM c) (0 ||| vP c)) (addM _ _ (0 ||| vM c) (0 ||| vP c))
      rw [Nat.zero_or, Nat.zero_or]
    · simp only [↓reduceIte, Bool.false_eq_true]
      change _ = mvL L _ _ (addP _ _ (vP c ||| 0) (vM c ||| 0)) (addM _ _ (vP c ||| 0) (vM c ||| 0))
      rw [Nat.or_zero, Nat.or_zero]
    · exact absurd ⟨h1, h2⟩ hxy

@[expose] noncomputable def packL (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih 256)) xs

theorem packL_spec : ∀ (xs : List Nat), (∀ x ∈ xs, x < 2 ^ 256) →
    packL xs < 2 ^ (256 * xs.length) ∧ ∀ k, laneOf k (packL xs) = xs.getD k 0
  | [], _ => ⟨by simp [packL], fun k => by simp [packL, laneOf_zero]⟩
  | x :: xs, h => by
    obtain ⟨ih1, ih2⟩ := packL_spec xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hx : x < 2 ^ 256 := h x List.mem_cons_self
    have e : packL (x :: xs) = 2 ^ 256 * packL xs + x := by
      change x ||| packL xs <<< 256 = _
      rw [Nat.or_comm, Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hx]
    refine ⟨?_, fun k => ?_⟩
    · rw [e, List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (256 * xs.length))]
      have : 2 ^ 256 * packL xs + x < 2 ^ 256 * packL xs + 2 ^ 256 := by omega
      have h2 : 2 ^ 256 * packL xs + 2 ^ 256 ≤ 2 ^ 256 * 2 ^ (256 * xs.length) := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ ih1
      omega
    · rw [e]
      cases k with
      | zero =>
        refine Nat.eq_of_testBit_eq fun i => ?_
        rw [testBit_laneOf, Nat.two_pow_add_eq_or_of_lt hx, Nat.testBit_or, Nat.testBit_two_pow_mul]
        simp only [List.getD_cons_zero, Nat.mul_zero, Nat.zero_add]
        by_cases hi : i < 256
        · have : ¬ i ≥ 256 := by omega
          simp [hi, this]
        · have h1 : x.testBit i = false := tb_false hx (by omega)
          simp [hi, h1]
      | succ k =>
        rw [List.getD_cons_succ, ← ih2 k]
        refine Nat.eq_of_testBit_eq fun i => ?_
        rw [testBit_laneOf, testBit_laneOf, Nat.two_pow_add_eq_or_of_lt hx, Nat.testBit_or,
          Nat.testBit_two_pow_mul]
        by_cases hi : i < 256
        · have h1 : x.testBit (256 * (k + 1) + i) = false := tb_false hx (by omega)
          have e2 : 256 * (k + 1) + i - 256 = 256 * k + i := by omega
          simp [hi, h1, e2, show 256 * (k + 1) + i ≥ 256 by omega]
        · simp [hi]

@[expose] noncomputable def ltAll (b : Nat) (xs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Bool.rec (motive := fun _ => Bool) false ih (Nat.blt x b)) xs

theorem ltAll_spec {b : Nat} : ∀ {xs : List Nat}, ltAll b xs = true → ∀ x ∈ xs, x < b
  | [], _ => by simp
  | x :: xs, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (ltAll b xs) (Nat.blt x b) = true := h
    cases hx : Nat.blt x b
    · rw [hx] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hx] at h'
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_of_ble_eq_true hx
      · exact ltAll_spec h' y hy

theorem mvL_of_lanes {L ps ms : List Nat} {n : Nat} (hn : n ≤ 256) (hL : L.length ≤ 256) (h1 : ltAll (2 ^ 256) ps = true)
    (h2 : ltAll (2 ^ 256) ms = true) (h3 : Nat.land (packL ps) (packL ms) = 0)
    (h4 : ltAll (2 ^ 256) (L.map vM) = true)
    (h5 : mvLW n (oneL n) L 0 (packL ps) (packL ms) 0 0 = packL ((List.range n).map (2 ^ ·))) :
    ∀ k < n, mvL L (ps.getD k 0) (ms.getD k 0) 0 0 = vmk (2 ^ k) 0 := by
  have hc : ∀ c ∈ L, vM c < 2 ^ 256 := fun c hc => ltAll_spec h4 _ (List.mem_map_of_mem hc)
  have hpos : (0 : Nat) < 2 ^ (256 * n) := Nat.two_pow_pos _
  obtain ⟨P, M, he, hP, hl⟩ := mvLW_spec n L 0 (packL ps) (packL ms) 0 0 (by omega) h3 hc hpos hpos
  have hid : ∀ x ∈ (List.range n).map (2 ^ ·), x < 2 ^ 256 := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact Nat.pow_lt_pow_right (by omega) (Nat.lt_of_lt_of_le (List.mem_range.mp hj) hn)
  obtain ⟨hI1, hI2⟩ := packL_spec _ hid
  rw [List.length_map, List.length_range] at hI1
  have e1 : Nat.lor P (Nat.shiftLeft M (Nat.mul 256 n)) = 2 ^ (256 * n) * M + P := by
    change P ||| M <<< (256 * n) = _
    rw [Nat.or_comm, Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hP]
  rw [← he, h5] at e1
  have hM : M = 0 := by
    have : 2 ^ (256 * n) * M < 2 ^ (256 * n) * 1 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  subst hM
  have hPe : P = packL ((List.range n).map (2 ^ ·)) := by omega
  intro k hk
  have := hl k hk
  rw [Nat.shiftRight_zero, Nat.shiftRight_zero, (packL_spec ps fun x hx => ltAll_spec h1 x hx).2,
    (packL_spec ms fun x hx => ltAll_spec h2 x hx).2, laneOf_zero, hPe, hI2] at this
  rw [this]
  congr 1
  simp [hk]

theorem mvLW_halves {L : List Nat} {n xp xm : Nat} (hL : L.length ≤ 256) (hd : Nat.land xp xm = 0)
    (hc : ltAll (2 ^ 256) (L.map vM) = true) (k : Nat) (hk : k < n) :
    mvL L (laneOf k xp) (laneOf k xm) 0 0 =
      vmk (laneOf k (mvLW n (oneL n) L 0 xp xm 0 0 % 2 ^ (256 * n)))
        (laneOf k (mvLW n (oneL n) L 0 xp xm 0 0 >>> (256 * n))) := by
  have hc' : ∀ c ∈ L, vM c < 2 ^ 256 := fun c hc' => ltAll_spec hc _ (List.mem_map_of_mem hc')
  have hpos : (0 : Nat) < 2 ^ (256 * n) := Nat.two_pow_pos _
  obtain ⟨P, M, he, hP, hl⟩ := mvLW_spec n L 0 xp xm 0 0 (by omega) hd hc' hpos hpos
  have e1 : Nat.lor P (Nat.shiftLeft M (Nat.mul 256 n)) = 2 ^ (256 * n) * M + P := by
    change P ||| M <<< (256 * n) = _
    rw [Nat.or_comm, Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hP]
  rw [he, e1, Nat.mul_add_mod, Nat.mod_eq_of_lt hP, Nat.shiftRight_eq_div_pow,
    Nat.mul_add_div hpos, Nat.div_eq_of_lt hP, Nat.add_zero]
  have := hl k hk
  rw [Nat.shiftRight_zero, Nat.shiftRight_zero, laneOf_zero] at this
  exact this

theorem halves_lor {s P M : Nat} (hP : P < 2 ^ s) :
    Nat.lor P (Nat.shiftLeft M s) % 2 ^ s = P ∧ Nat.lor P (Nat.shiftLeft M s) >>> s = M := by
  have e1 : Nat.lor P (Nat.shiftLeft M s) = 2 ^ s * M + P := by
    change P ||| M <<< s = _
    rw [Nat.or_comm, Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt hP]
  rw [e1, Nat.mul_add_mod, Nat.mod_eq_of_lt hP, Nat.shiftRight_eq_div_pow,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hP, Nat.add_zero]
  exact ⟨rfl, rfl⟩

theorem laneOf_packL_range {n : Nat} {f : Nat → Nat}
    (h : ltAll (2 ^ 256) ((List.range n).map f) = true) {j : Nat} (hj : j < n) :
    laneOf j (packL ((List.range n).map f)) = f j := by
  rw [(packL_spec _ fun x hx => ltAll_spec h x hx).2]
  simp [hj]

end CFSG.KS.ONLane

end
