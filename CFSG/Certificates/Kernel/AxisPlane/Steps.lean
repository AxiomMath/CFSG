module

public import CFSG.Certificates.Kernel.AxisPlane.Sound
public import Certificates.Data.CFSGNative.MonsterAxis.Cover

public section

set_option maxHeartbeats 400000

namespace CFSG.KC.AxisPlane

open CFSG.KC.Benes CFSG.KC.MonsterConv.Perm

@[expose] def tvC (c v : Nat) : Nat := tvN (Nat.land c 31) (Nat.shiftRight c 5) v

theorem disj_tmask {t l : Nat} (ht : t < 24) : Disj (2 ^ t) (Nat.shiftRight (tmaskK t l) 64) := by
  intro p hp
  rw [← dat_eq_shr, dat_tmaskK ht] at hp ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp
  have h : (p + 2 ^ t).testBit t = true := by
    rw [add_two_pow_eq_xor hp.1.2, Nat.testBit_xor, Nat.testBit_two_pow, hp.1.2]
    simp
  simp [h]

theorem dat_tvK {c : Nat} (hc : opValid c = true) (S : Nat) {q : Nat} (hq : q < 16777216) :
    dat (tvK c S) q = dat S (tvC c q) := by
  obtain ⟨ht, -, hl⟩ := opValid_spec hc
  have ht' : Nat.land c 31 < 24 := ht
  have hl' : (Nat.shiftRight c 5).testBit (Nat.land c 31) = false := hl
  have e : tvK c S = swK (2 ^ Nat.land c 31) (tmaskK (Nat.land c 31) (Nat.shiftRight c 5)) S := by
    unfold tvK
    rw [nshl, Nat.one_shiftLeft]
  rw [e, dat_eq_shr, swK_shr, testBit_dsw (disj_tmask ht'), ← dat_eq_shr, swp_eq_tvN ht' hl' hq]
  rfl

theorem tvC_lt {c : Nat} (hc : opValid c = true) {v : Nat} (hv : v < 16777216) :
    tvC c v < 16777216 :=
  tvN_lt (opValid_spec hc).1 hv

theorem tvC_tvC {c : Nat} (hc : opValid c = true) (v : Nat) : tvC c (tvC c v) = v :=
  tvN_tvN (opValid_spec hc).2.2 v

theorem tvC_xor (c a b : Nat) : tvC c (a ^^^ b) = tvC c a ^^^ tvC c b := tvN_xor _ _ a b

@[expose] def piOps : List Nat → Nat → Nat
  | [], q => q
  | c :: r, q => tvC c (piOps r q)

theorem opsValid_cons {c : Nat} {r : List Nat} (h : opsValid (c :: r) = true) :
    opValid c = true ∧ opsValid r = true := andB_true h

theorem piOps_lt : ∀ {ops : List Nat}, opsValid ops = true → ∀ {q : Nat}, q < 16777216 →
    piOps ops q < 16777216
  | [], _, _, hq => hq
  | _ :: _, h, _, hq => tvC_lt (opsValid_cons h).1 (piOps_lt (opsValid_cons h).2 hq)

theorem dat_applyK : ∀ {ops : List Nat}, opsValid ops = true → ∀ (S : Nat) {q : Nat},
    q < 16777216 → dat (applyK ops S) q = dat S (piOps ops q)
  | [], _, _, _, _ => rfl
  | c :: r, h, S, q, hq => by
    have e : applyK (c :: r) S = applyK r (tvK c S) := rfl
    rw [e, dat_applyK (opsValid_cons h).2 _ hq,
      dat_tvK (opsValid_cons h).1 _ (piOps_lt (opsValid_cons h).2 hq)]
    rfl

theorem par24_rec (l v : Nat) : ∀ k, k ≤ 24 →
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Nat.xor acc (Nat.land (Nat.shiftRight (Nat.land l v) j) (nat_lit 1))) k =
      (parG l v k).toNat
  | 0, _ => rfl
  | k + 1, hk => by
    change Nat.xor (Nat.rec (motive := fun _ => Nat) 0 _ k)
      (Nat.land (Nat.shiftRight (Nat.land l v) k) 1) = _
    rw [par24_rec l v k (by omega), land_shr_one, nland, Nat.testBit_and, parG]
    cases parG l v k <;> cases l.testBit k <;> cases v.testBit k <;> rfl

theorem tvV_eq (c v : Nat) : tvV c v = tvC c v := by
  unfold tvV tvC tvN
  have e : par24 (Nat.land (Nat.shiftRight c 5) v) = (parG (Nat.shiftRight c 5) v 24).toNat :=
    par24_rec _ _ 24 (Nat.le_refl 24)
  rw [e, nxor]
  cases parG (Nat.shiftRight c 5) v 24
  · simp
  · simp [Nat.one_shiftLeft]

theorem vecOps_cons (c : Nat) (r : List Nat) (v : Nat) :
    vecOps (c :: r) v = vecOps r (tvC c v) := by
  rw [← tvV_eq]
  rfl

theorem vecOps_xor : ∀ (ops : List Nat) (a b : Nat),
    vecOps ops (a ^^^ b) = vecOps ops a ^^^ vecOps ops b
  | [], _, _ => rfl
  | c :: r, a, b => by rw [vecOps_cons, vecOps_cons, vecOps_cons, tvC_xor, vecOps_xor r]

theorem vecOps_zero : ∀ (ops : List Nat), vecOps ops 0 = 0
  | [] => rfl
  | c :: r => by
    rw [vecOps_cons]
    unfold tvC
    rw [tvN_zero, vecOps_zero r]

theorem vecOps_lt : ∀ {ops : List Nat}, opsValid ops = true → ∀ {v : Nat}, v < 16777216 →
    vecOps ops v < 16777216
  | [], _, _, hv => hv
  | c :: r, h, v, hv => by
    rw [vecOps_cons]
    exact vecOps_lt (opsValid_cons h).2 (tvC_lt (opsValid_cons h).1 hv)

theorem piOps_vecOps : ∀ {ops : List Nat}, opsValid ops = true → ∀ (v : Nat),
    piOps ops (vecOps ops v) = v
  | [], _, _ => rfl
  | c :: r, h, v => by
    rw [vecOps_cons]
    change tvC c (piOps r (vecOps r (tvC c v))) = v
    rw [piOps_vecOps (opsValid_cons h).2, tvC_tvC (opsValid_cons h).1]

theorem vecOps_piOps : ∀ {ops : List Nat}, opsValid ops = true → ∀ (q : Nat),
    vecOps ops (piOps ops q) = q
  | [], _, _ => rfl
  | c :: r, h, q => by
    change vecOps (c :: r) (tvC c (piOps r q)) = q
    rw [vecOps_cons, tvC_tvC (opsValid_cons h).1, vecOps_piOps (opsValid_cons h).2]

theorem rowsGo_spec (ops : List Nat) : ∀ (rl : List Nat) (j : Nat), rowsGo ops rl j = true →
    j + rl.length = 24 ∧ ∀ k < rl.length, rl.getD k 0 = vecOps ops (2 ^ (j + k))
  | [], j, h => by
    have : Nat.beq j 24 = true := h
    rw [Nat.beq_eq] at this
    exact ⟨by simpa using this, fun k hk => absurd hk (by simp)⟩
  | r :: rl, j, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    rw [Nat.beq_eq, nshl, Nat.one_shiftLeft] at h1
    obtain ⟨ih1, ih2⟩ := rowsGo_spec ops rl (j + 1) h2
    refine ⟨by simp; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · simpa using h1.symm
    · have := ih2 k (by simpa using hk)
      simpa [show j + 1 + k = j + (k + 1) by omega] using this

theorem mod_two_pow_succ_xor (v n : Nat) :
    v % 2 ^ (n + 1) = v % 2 ^ n ^^^ (if v.testBit n = true then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  split
  · next h =>
    rw [Nat.testBit_two_pow]
    by_cases hj : j = n
    · subst hj
      simp [h]
    · by_cases hj' : j < n
      · simp [hj', show j < n + 1 by omega, Ne.symm hj]
      · simp [hj', Ne.symm hj, show ¬ j < n + 1 by omega]
  · next h =>
    rw [Nat.zero_testBit, Bool.xor_false]
    by_cases hj : j = n
    · subst hj
      simp [h]
    · by_cases hj' : j < n
      · simp [hj', show j < n + 1 by omega]
      · simp [hj', show ¬ j < n + 1 by omega]

theorem actGo_spec {ops : List Nat} {rows : Array Nat}
    (hr : ∀ i < 24, rows[i]! = vecOps ops (2 ^ i)) (v : Nat) :
    ∀ n, n ≤ 24 → ∀ acc,
      CFSG.Monster.AxisCount.Native.Cover.actGo rows v n acc = acc ^^^ vecOps ops (v % 2 ^ n)
  | 0, _, acc => by
    rw [CFSG.Monster.AxisCount.Native.Cover.actGo, Nat.pow_zero, Nat.mod_one, vecOps_zero,
      Nat.xor_zero]
  | n + 1, hn, acc => by
    rw [CFSG.Monster.AxisCount.Native.Cover.actGo, actGo_spec hr v n (by omega),
      mod_two_pow_succ_xor, vecOps_xor]
    split
    · rw [hr n (by omega), Nat.xor_assoc, Nat.xor_comm (vecOps ops (2 ^ n))]
    · rw [vecOps_zero, Nat.xor_zero]

theorem actRows_eq_vecOps {ops rl : List Nat} (h : opsOK ops rl = true) {x : Nat}
    (hx : x < 16777216) :
    CFSG.Monster.AxisCount.Native.Cover.actRows rl.toArray x = vecOps ops x := by
  obtain ⟨-, h2⟩ := andB_true h
  obtain ⟨hlen, hget⟩ := rowsGo_spec ops rl 0 h2
  have hr : ∀ i < 24, rl.toArray[i]! = vecOps ops (2 ^ i) := by
    intro i hi
    have := hget i (by omega)
    rw [Nat.zero_add] at this
    rw [← this]
    simp [getElem!_pos, List.getD_eq_getElem?_getD, show i < rl.length by omega]
  unfold CFSG.Monster.AxisCount.Native.Cover.actRows
  rw [actGo_spec hr x 24 (Nat.le_refl 24), Nat.zero_xor, Nat.mod_eq_of_lt (by exact hx)]

theorem codeAt_nil (x : Nat) : codeAt [] x = 0 := rfl

theorem codeAt_cons (P : Nat) (Ps : List Nat) (x : Nat) :
    codeAt (P :: Ps) x = (dat P x).toNat + 2 * codeAt Ps x := by
  change Nat.add (bitAt P x) (Nat.shiftLeft (codeAt Ps x) 1) = _
  rw [bitAt, land_shr_one, nadd, nshl, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
  rfl

theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem codeAt_lt : ∀ (Ps : List Nat) (x : Nat), codeAt Ps x < 2 ^ Ps.length
  | [], _ => by simp [codeAt_nil]
  | P :: Ps, x => by
    rw [codeAt_cons, List.length_cons, Nat.pow_succ]
    have := codeAt_lt Ps x
    have := toNat_le_one (dat P x)
    omega

theorem codeAt_eq_zero : ∀ (Ps : List Nat) (x : Nat),
    codeAt Ps x = 0 ↔ ∀ P ∈ Ps, dat P x = false
  | [], _ => by simp [codeAt_nil]
  | P :: Ps, x => by
    rw [codeAt_cons, List.forall_mem_cons, ← codeAt_eq_zero Ps x]
    cases dat P x <;> simp <;> omega

theorem dat_codeK : ∀ (Ps : List Nat) (c q : Nat),
    dat (codeK Ps c) q = (decide (q < 16777216) && decide (codeAt Ps q = c % 2 ^ Ps.length))
  | [], c, q => by
    change dat (Nat.lor allK (saltK (Nat.add c 128))) q = _
    rw [dat_lor, dat_allK, dat_salt, codeAt_nil]
    simp [Nat.mod_one]
  | P :: Ps, c, q => by
    change dat (Nat.land (Bool.rec (motive := fun _ => Nat) (Nat.xor allK P) P
      (Nat.beq (Nat.land c 1) 1)) (codeK Ps (Nat.shiftRight c 1))) q = _
    have hc : Nat.beq (Nat.land c 1) 1 = decide (c % 2 = 1) := by
      rw [nland, Nat.and_one_is_mod]
      cases Nat.mod_two_eq_zero_or_one c with
      | inl h => rw [h]; rfl
      | inr h => rw [h]; rfl
    have hmod : c % 2 ^ (P :: Ps).length =
        (decide (c % 2 = 1)).toNat + 2 * (c / 2 % 2 ^ Ps.length) := by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm _ 2, Nat.mod_mul]
      rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]
    have key : ∀ (b r : Bool) (A B : Nat),
        decide (b.toNat + 2 * A = r.toNat + 2 * B) = ((b == r) && decide (A = B)) := by
      intro b r A B
      cases b <;> cases r <;> simp <;> omega
    rw [dat_land, hc, dat_codeK Ps, codeAt_cons, hmod, key, nshr, Nat.shiftRight_eq_div_pow,
      Nat.pow_one]
    cases decide (c % 2 = 1)
    · change (dat (Nat.xor allK P) q && _) = _
      rw [dat_xor, dat_allK]
      cases dat P q <;> cases decide (q < 16777216) <;>
        cases decide (codeAt Ps q = c / 2 % 2 ^ Ps.length) <;> rfl
    · change (dat P q && _) = _
      cases dat P q <;> cases decide (q < 16777216) <;>
        cases decide (codeAt Ps q = c / 2 % 2 ^ Ps.length) <;> rfl

theorem dat_anyK : ∀ (Ps : List Nat) (q : Nat), dat (anyK Ps) q = true ↔ ∃ P ∈ Ps, dat P q = true
  | [], q => by simp [anyK, dat_zero]
  | P :: Ps, q => by
    change dat (Nat.lor P (anyK Ps)) q = true ↔ _
    rw [dat_lor, Bool.or_eq_true, dat_anyK Ps]
    simp

theorem subK_spec {X Y : Nat} (h : subK X Y = true) {q : Nat} (hq : q < 16777216)
    (hx : dat X q = true) : dat Y q = true := by
  rw [subK, Nat.beq_eq] at h
  have := congrArg (fun z => dat z q) h
  simp only [dat_land, dat_xor, dat_allK, dat_zero, hx, decide_eq_true hq] at this
  simpa using this

theorem dat_incK : ∀ (Qs Rs : List Nat), Qs.length = Rs.length → ∀ (C q : Nat), q < 16777216 →
    dat (incK Qs Rs C) q = decide (codeAt Qs q = codeAt Rs q + (dat C q).toNat)
  | [], [], _, C, q, hq => by
    change dat (Nat.xor allK C) q = _
    rw [dat_xor, dat_allK, decide_eq_true hq]
    change _ = decide (0 = 0 + (dat C q).toNat)
    cases dat C q <;> simp
  | Q :: Qs, R :: Rs, hl, C, q, hq => by
    change dat (Nat.land (Nat.xor allK (Nat.xor Q (Nat.xor R C))) (incK Qs Rs (Nat.land R C))) q = _
    rw [dat_land, dat_xor, dat_xor, dat_xor, dat_allK, decide_eq_true hq,
      dat_incK Qs Rs (by simpa using hl) _ q hq, dat_land, codeAt_cons, codeAt_cons]
    cases dat Q q <;> cases dat R q <;> cases dat C q <;> simp <;> omega
  | [], _ :: _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], hl, _, _, _ => absurd hl (by simp)

end CFSG.KC.AxisPlane

end
