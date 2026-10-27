module

public import CFSG.Certificates.Kernel.LyOmega.SoundB6Trunc

public section
namespace CFSG.KS.LyOm.SB6
open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KS.LyOm CFSG.KC.Loop

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem nIf_eq (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

private theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

private theorem fldW_eq (r o w : ℕ) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem shr6 (i : ℕ) : Nat.shiftRight i 6 = i / 64 := by
  change i >>> 6 = _
  rw [Nat.shiftRight_eq_div_pow]

private theorem land63 (i : ℕ) : Nat.land i 63 = i % 64 := by
  change i &&& 63 = _
  have : (63 : ℕ) = 2 ^ 6 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

private theorem land20 (e : ℕ) : Nat.land e 1048575 = e % 2 ^ 20 := by
  change e &&& 1048575 = _
  have : (1048575 : ℕ) = 2 ^ 20 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

private theorem shr20 (e : ℕ) : Nat.shiftRight e 20 = e / 2 ^ 20 := by
  change e >>> 20 = _
  rw [Nat.shiftRight_eq_div_pow]

private theorem shl6 (b : ℕ) : Nat.shiftLeft b 6 = 64 * b := by
  change b <<< 6 = _
  rw [Nat.shiftLeft_eq]; omega

private theorem getRec_eq (blk : ℕ → ℕ) (RB i : ℕ) :
    getRec blk RB i = blk (i / 64) / 2 ^ ((i % 64) * RB) % 2 ^ RB := by
  unfold getRec
  rw [strictN_eq', fldW_eq, shr6, land63]
  rfl

private theorem recAnd_iff (g : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (g l)) n = true ↔
      ∀ l < n, g l = true
  | 0 => ⟨fun _ l hl => absurd hl (Nat.not_lt_zero l), fun _ => rfl⟩
  | n + 1 => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun l ih => Bool.rec (motive := fun _ => Bool) false ih (g l)) n) (g n) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, recAnd_iff g n]
    constructor
    · rintro ⟨h1, h2⟩ l hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
      · exact h2 l h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun l hl => h l (Nat.lt_succ_of_lt hl)⟩

private theorem lane_mod (Y N b c : ℕ) (h : b + c ≤ N) :
    (Y % 2 ^ N) / 2 ^ b % 2 ^ c = Y / 2 ^ b % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < c
  · have h1 : b + i < N := by omega
    have h2 : i + b < N := by omega
    simp [hi, h1, h2]
  · simp [hi]

private noncomputable def cntB (c : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | r + 1 => cntB c r + if c r = true then 1 else 0

private theorem cntB_zero (c : ℕ → Bool) : cntB c 0 = 0 := rfl

private theorem cntB_succ (c : ℕ → Bool) (r : ℕ) :
    cntB c (r + 1) = cntB c r + if c r = true then 1 else 0 := rfl

private theorem cntB_le (c : ℕ → Bool) : ∀ r, cntB c r ≤ r
  | 0 => le_rfl
  | r + 1 => by
    rw [cntB_succ]
    have := cntB_le c r
    split_ifs <;> omega

private theorem cntB_mono (c : ℕ → Bool) {r1 r2 : ℕ} (h : r1 ≤ r2) : cntB c r1 ≤ cntB c r2 := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [cntB_succ]; omega

private theorem cnt_exists (c : ℕ → Bool) : ∀ N t, t < cntB c N →
    ∃ r, r < N ∧ c r = true ∧ cntB c r = t
  | 0, t, h => by simp [cntB_zero] at h
  | N + 1, t, h => by
    rw [cntB_succ] at h
    by_cases hc : c N = true
    · rw [if_pos hc] at h
      by_cases ht : t < cntB c N
      · obtain ⟨r, hr, h1, h2⟩ := cnt_exists c N t ht
        exact ⟨r, by omega, h1, h2⟩
      · exact ⟨N, by omega, hc, by omega⟩
    · rw [if_neg hc] at h
      obtain ⟨r, hr, h1, h2⟩ := cnt_exists c N t h
      exact ⟨r, by omega, h1, h2⟩

private noncomputable def GR (c : ℕ → Bool) (v : ℕ → ℕ) (T : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun acc _ => acc)
    (fun k ih acc cnt => Bool.rec (motive := fun _ => ℕ) (ih acc cnt)
      (ih (Nat.lor acc (Nat.shiftLeft (v (Nat.sub (nat_lit 63) k)) (Nat.mul (nat_lit 539) cnt)))
        (Nat.succ cnt)) (c (Nat.sub (nat_lit 63) k))) T

private theorem GR_zero (c : ℕ → Bool) (v : ℕ → ℕ) (acc cnt : ℕ) : GR c v 0 acc cnt = acc := rfl

private theorem GR_succ (c : ℕ → Bool) (v : ℕ → ℕ) (t acc cnt : ℕ) :
    GR c v (t + 1) acc cnt = Bool.rec (motive := fun _ => ℕ) (GR c v t acc cnt)
      (GR c v t (Nat.lor acc (Nat.shiftLeft (v (Nat.sub (nat_lit 63) t)) (Nat.mul (nat_lit 539) cnt)))
        (Nat.succ cnt)) (c (Nat.sub (nat_lit 63) t)) := rfl

private theorem lor_eq_add {acc x k : ℕ} (h : acc < 2 ^ k) :
    Nat.lor acc (Nat.shiftLeft x k) = x * 2 ^ k + acc := by
  change acc ||| (x <<< k) = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]

private theorem GR_spec (c : ℕ → Bool) (v : ℕ → ℕ) (hv : ∀ r, v r < 2 ^ 539) :
    ∀ t r0, t + r0 = 64 → ∀ acc, acc < 2 ^ (539 * cntB c r0) →
      GR c v t acc (cntB c r0) % 2 ^ (539 * cntB c r0) = acc ∧
      ∀ r, r0 ≤ r → r < 64 → c r = true →
        GR c v t acc (cntB c r0) / 2 ^ (539 * cntB c r) % 2 ^ 539 = v r
  | 0, r0, ht, acc, hacc => by
    have : r0 = 64 := by omega
    subst this
    refine ⟨?_, fun r h1 h2 _ => by omega⟩
    rw [GR_zero]
    exact Nat.mod_eq_of_lt hacc
  | t + 1, r0, ht, acc, hacc => by
    have e : (63 - t : ℕ) = r0 := by omega
    have e' : Nat.sub (nat_lit 63) t = r0 := e
    by_cases hcr : c r0 = true
    · have hcn : cntB c (r0 + 1) = cntB c r0 + 1 := by rw [cntB_succ, if_pos hcr]
      have hP : 0 < 2 ^ (539 * cntB c r0) := Nat.two_pow_pos _
      have e2 : 2 ^ (539 * (cntB c r0 + 1)) = 2 ^ (539 * cntB c r0) * 2 ^ 539 := by
        rw [Nat.mul_succ, pow_add]
      have hvr := hv r0
      have hacc' : v r0 * 2 ^ (539 * cntB c r0) + acc < 2 ^ (539 * cntB c (r0 + 1)) := by
        rw [hcn, e2]
        have h3 := Nat.mul_le_mul_right (2 ^ (539 * cntB c r0)) (Nat.succ_le_of_lt hvr)
        rw [Nat.succ_mul] at h3
        omega
      obtain ⟨ih1, ih2⟩ := GR_spec c v hv t (r0 + 1) (by omega)
        (v r0 * 2 ^ (539 * cntB c r0) + acc) hacc'
      rw [hcn] at ih1 ih2
      have key : GR c v (t + 1) acc (cntB c r0) =
          GR c v t (v r0 * 2 ^ (539 * cntB c r0) + acc) (cntB c r0 + 1) := by
        rw [GR_succ, e', hcr]
        exact congrArg (fun a => GR c v t a (cntB c r0 + 1))
          (lor_eq_add (x := v r0) (k := 539 * cntB c r0) hacc)
      rw [key]
      have hmod : GR c v t (v r0 * 2 ^ (539 * cntB c r0) + acc) (cntB c r0 + 1) %
          2 ^ (539 * cntB c r0) = acc := by
        rw [← Nat.mod_mod_of_dvd _ (show 2 ^ (539 * cntB c r0) ∣ 2 ^ (539 * (cntB c r0 + 1)) from
          pow_dvd_pow 2 (by omega)), ih1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hacc]
      refine ⟨hmod, fun r hr1 hr2 hcr' => ?_⟩
      rcases Nat.eq_or_lt_of_le hr1 with rfl | hlt
      · rw [e2] at ih1
        rw [← Nat.mod_mul_right_div_self, ih1, Nat.mul_comm (v r0), Nat.mul_add_div hP, Nat.div_eq_of_lt hacc,
          Nat.add_zero]
      · exact ih2 r hlt hr2 hcr'
    · have hcf : c r0 = false := by simpa using hcr
      have hcn : cntB c (r0 + 1) = cntB c r0 := by rw [cntB_succ, if_neg hcr]; rfl
      obtain ⟨ih1, ih2⟩ := GR_spec c v hv t (r0 + 1) (by omega) acc (by rw [hcn]; exact hacc)
      rw [hcn] at ih1 ih2
      have key : GR c v (t + 1) acc (cntB c r0) = GR c v t acc (cntB c r0) := by
        rw [GR_succ, e', hcf]
      rw [key]
      refine ⟨ih1, fun r hr1 hr2 hcr' => ?_⟩
      rcases Nat.eq_or_lt_of_le hr1 with rfl | hlt
      · exact absurd hcr' hcr
      · exact ih2 r hlt hr2 hcr'

private theorem core {C : SConsts} (hC : sConstsOK C = true)
    (hBlk : ∀ {r X K : ℕ}, r ≤ 64 → LCanon 11 r 49 X → LCanon 11 49 49 K →
      LCanon 11 r 49 (sBlk C X K) ∧ ∀ q < r, vec49 (sBlk C X K / 2 ^ (539 * q)) =
        Matrix.vecMul (vec49 (X / 2 ^ (539 * q))) (kM K))
    {c : ℕ → Bool} {vF vT : ℕ → ℕ} (hvF : ∀ r, vF r < 2 ^ 539) (hvT : ∀ r, vT r < 2 ^ 539)
    {K : ℕ} (hK : LCanon 11 49 49 K)
    (hEq : sBlk C (GR c vF 64 0 0) K = GR c vT 64 0 0) {r : ℕ} (hr : r < 64) (hcr : c r = true)
    (hpar : ∀ r', r' ≤ r → c r' = true → LCanon 11 1 49 (vF r')) :
    LCanon 11 1 49 (vT r) ∧ vec49 (vT r) = Matrix.vecMul (vec49 (vF r)) (kM K) := by
  have h0 : (0 : ℕ) < 2 ^ (539 * cntB c 0) := by rw [cntB_zero]; simp
  have spF := GR_spec c vF hvF 64 0 (by norm_num) 0 h0
  have spT := GR_spec c vT hvT 64 0 (by norm_num) 0 h0
  rw [cntB_zero] at spF spT
  obtain ⟨-, spF⟩ := spF
  obtain ⟨-, spT⟩ := spT
  generalize hgF : GR c vF 64 0 0 = gF at hEq spF
  generalize hgT : GR c vT 64 0 0 = gT at hEq spT
  obtain ⟨q, hqq⟩ : ∃ q, cntB c r = q := ⟨_, rfl⟩
  have hq : q ≤ r := hqq ▸ cntB_le c r
  have hq1 : q + 1 ≤ 64 := by omega
  have e2 : 2 ^ (539 * (q + 1)) = 2 ^ (539 * q) * 2 ^ 539 := by rw [Nat.mul_succ, pow_add]
  have hQ : 11 * 49 * (q + 1) = 539 * (q + 1) := by ring
  have rowF : ∀ t, t ≤ q → ∃ r', r' ≤ r ∧ c r' = true ∧ gF / 2 ^ (539 * t) % 2 ^ 539 = vF r' := by
    intro t ht
    have ht' : t < cntB c (r + 1) := by rw [cntB_succ, if_pos hcr]; omega
    obtain ⟨r', hr', h1, h2⟩ := cnt_exists c (r + 1) t ht'
    refine ⟨r', by omega, h1, ?_⟩
    have := spF r' (Nat.zero_le _) (by omega) h1
    rw [h2] at this
    exact this
  have rowT : gT / 2 ^ (539 * q) % 2 ^ 539 = vT r := by
    have := spT r (Nat.zero_le _) hr hcr
    rwa [hqq] at this
  have rowFq : gF / 2 ^ (539 * q) % 2 ^ 539 = vF r := by
    have := spF r (Nat.zero_le _) hr hcr
    rwa [hqq] at this
  have hZF : LCanon 11 (q + 1) 49 (gF % 2 ^ (539 * (q + 1))) := by
    refine ⟨?_, fun t ht j hj => ?_⟩
    · rw [hQ]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · obtain ⟨r', hr', hc', hrow⟩ := rowF t (by omega)
      have hpc := (hpar r' hr' hc').2 0 (by norm_num) j hj
      have key : gF % 2 ^ (539 * (q + 1)) / 2 ^ (11 * 49 * t + 11 * j) % 2 ^ 11 =
          vF r' / 2 ^ (11 * j) % 2 ^ 11 := by
        have e3 : 11 * 49 * t + 11 * j = 539 * t + 11 * j := by ring
        rw [e3, lane_mod gF (539 * (q + 1)) (539 * t + 11 * j) 11 (by omega), pow_add,
          ← Nat.div_div_eq_div_mul,
          ← lane_mod (gF / 2 ^ (539 * t)) 539 (11 * j) 11 (by omega), hrow]
      rw [key]
      have e4 : 11 * 49 * 0 + 11 * j = 11 * j := by ring
      rw [e4] at hpc
      exact hpc
  obtain ⟨hcan, hvec⟩ := hBlk hq1 hZF hK
  have htr := CFSG.KS.LyOm.SB6T.sBlk_trunc hC (c := q + 1) (X := gF) (K := K) hq1
  rw [hEq] at htr
  have hlt : sBlk C (gF % 2 ^ (539 * (q + 1))) K < 2 ^ (539 * (q + 1)) := by
    have := hcan.1
    rwa [hQ] at this
  rw [Nat.mod_eq_of_lt hlt] at htr
  have hZTrow : sBlk C (gF % 2 ^ (539 * (q + 1))) K / 2 ^ (539 * q) = vT r := by
    rw [← htr, e2, Nat.mod_mul_right_div_self]
    exact rowT
  have hZFrow : gF % 2 ^ (539 * (q + 1)) / 2 ^ (539 * q) = vF r := by
    rw [e2, Nat.mod_mul_right_div_self]
    exact rowFq
  refine ⟨⟨?_, fun i hi j hj => ?_⟩, ?_⟩
  · have : 11 * 49 * 1 = 539 := by norm_num
    rw [this]
    exact hvT r
  · have hi0 : i = 0 := by omega
    subst hi0
    have := hcan.2 q (by omega) j hj
    have e3 : 11 * 49 * q + 11 * j = 539 * q + 11 * j := by ring
    rw [e3, pow_add, ← Nat.div_div_eq_div_mul, hZTrow] at this
    have e4 : 11 * 49 * 0 + 11 * j = 11 * j := by ring
    rw [e4]
    exact this
  · have := hvec q (by omega)
    rw [hZTrow, hZFrow] at this
    exact this

private noncomputable def cF (PT : ℕ → ℕ) (n b s : ℕ) (r : ℕ) : Bool :=
  bAnd(isChild n (Nat.add (Nat.shiftLeft b (nat_lit 6)) r),
    Nat.beq (Nat.shiftRight (fldW (PT b) (Nat.mul (nat_lit 22) r) (nat_lit 22)) (nat_lit 20)) s)

private noncomputable def vG (KX PT : ℕ → ℕ) (b : ℕ) (self : Bool) (r : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (getRec KX (nat_lit 539) (Nat.land (fldW (PT b) (Nat.mul (nat_lit 22) r) (nat_lit 22))
      (nat_lit 1048575)))
    (fldW (KX b) (Nat.mul (nat_lit 539) r) (nat_lit 539)) self

private noncomputable def GS (E : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (vv : ℕ → ℕ → ℕ) (T : ℕ) :
    ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun acc _ => acc)
    (fun k ih acc cnt =>
      (fun r => strictN (E r) (fun e => Bool.rec (motive := fun _ => ℕ) (ih acc cnt)
        (ih (Nat.lor acc (Nat.shiftLeft (vv r e) (Nat.mul (nat_lit 539) cnt))) (Nat.succ cnt))
        (cc r e))) (Nat.sub (nat_lit 63) k)) T

private theorem GS_eq (E : ℕ → ℕ) (cc : ℕ → ℕ → Bool) (vv : ℕ → ℕ → ℕ) :
    ∀ T acc cnt, GS E cc vv T acc cnt = GR (fun r => cc r (E r)) (fun r => vv r (E r)) T acc cnt
  | 0, acc, cnt => rfl
  | T + 1, acc, cnt => by
    have h : GS E cc vv (T + 1) acc cnt =
        strictN (E (Nat.sub (nat_lit 63) T)) (fun e => Bool.rec (motive := fun _ => ℕ)
          (GS E cc vv T acc cnt)
          (GS E cc vv T (Nat.lor acc (Nat.shiftLeft (vv (Nat.sub (nat_lit 63) T) e)
            (Nat.mul (nat_lit 539) cnt))) (Nat.succ cnt))
          (cc (Nat.sub (nat_lit 63) T) e)) := rfl
    rw [h, strictN_eq', GR_succ, GS_eq E cc vv T, GS_eq E cc vv T]

private noncomputable def GSX (KX PT : Nat → Nat) (n b s : Nat) (self : Bool) (T : Nat) : Nat :=
  strictN (PT b) (fun P => strictN (KX b) (fun K =>
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
      (fun k ih acc cnt =>
        (fun r => strictN (fldW P (Nat.mul (nat_lit 22) r) (nat_lit 22)) (fun e =>
          nIf(bAnd(isChild n (Nat.add (Nat.shiftLeft b (nat_lit 6)) r),
              Nat.beq (Nat.shiftRight e (nat_lit 20)) s),
            ih (Nat.lor acc (Nat.shiftLeft
              (Bool.rec (motive := fun _ => Nat)
                (getRec KX (nat_lit 539) (Nat.land e (nat_lit 1048575)))
                (fldW K (Nat.mul (nat_lit 539) r) (nat_lit 539)) self)
              (Nat.mul (nat_lit 539) cnt))) (Nat.succ cnt),
            ih acc cnt)))
        (Nat.sub (nat_lit 63) k))
      T (nat_lit 0) (nat_lit 0)))

private theorem sGather_GSX (KX PT : ℕ → ℕ) (n b s : ℕ) (self : Bool) :
    sGather KX PT n b s self = GSX KX PT n b s self (nat_lit 64) := rfl

private theorem GSX_eq (KX PT : ℕ → ℕ) (n b s : ℕ) (self : Bool) (T : ℕ) :
    GSX KX PT n b s self T = GR (cF PT n b s) (vG KX PT b self) T 0 0 := by
  unfold GSX
  rw [strictN_eq', strictN_eq']
  exact GS_eq (fun r => fldW (PT b) (Nat.mul (nat_lit 22) r) (nat_lit 22))
    (fun r e => bAnd(isChild n (Nat.add (Nat.shiftLeft b (nat_lit 6)) r),
      Nat.beq (Nat.shiftRight e (nat_lit 20)) s))
    (fun r e => Bool.rec (motive := fun _ => ℕ)
      (getRec KX (nat_lit 539) (Nat.land e (nat_lit 1048575)))
      (fldW (KX b) (Nat.mul (nat_lit 539) r) (nat_lit 539)) self) T 0 0

private theorem sGather_eq (KX PT : ℕ → ℕ) (n b s : ℕ) (self : Bool) :
    sGather KX PT n b s self = GR (cF PT n b s) (vG KX PT b self) (nat_lit 64) 0 0 :=
  (sGather_GSX KX PT n b s self).trans (GSX_eq KX PT n b s self _)

private noncomputable def BadR (P m n b T : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => (fun i => (fun e => nIf(isChild n i,
        nIf(bAnd(Nat.blt (Nat.land e (nat_lit 1048575)) i, Nat.blt (Nat.shiftRight e (nat_lit 20)) m),
          acc, Nat.succ acc), acc))
        (fldW P (Nat.mul (nat_lit 22) r) (nat_lit 22)))
      (Nat.add (Nat.shiftLeft b (nat_lit 6)) r)) T

private theorem sBad_eq (PT : ℕ → ℕ) (m n b : ℕ) :
    sBad PT m n b = BadR (PT b) m n b (nat_lit 64) := by
  have h : sBad PT m n b = strictN (PT b) (fun P => BadR P m n b (nat_lit 64)) := rfl
  rw [h, strictN_eq']

private theorem isChild_iff (n b r : ℕ) :
    isChild n (Nat.add (Nat.shiftLeft b 6) r) = true ↔ 0 < 64 * b + r ∧ 64 * b + r < n := by
  unfold isChild
  rw [bAnd_eq, Bool.and_eq_true, blt_iff, blt_iff]
  have : Nat.add (Nat.shiftLeft b 6) r = 64 * b + r := by
    rw [shl6]; rfl
  rw [this]

private noncomputable def badStep (P m n b r acc : ℕ) : ℕ :=
  (fun i => (fun e => nIf(isChild n i,
        nIf(bAnd(Nat.blt (Nat.land e (nat_lit 1048575)) i, Nat.blt (Nat.shiftRight e (nat_lit 20)) m),
          acc, Nat.succ acc), acc))
    (fldW P (Nat.mul (nat_lit 22) r) (nat_lit 22)))
  (Nat.add (Nat.shiftLeft b (nat_lit 6)) r)

private theorem BadR_spec (P m n b : ℕ) : ∀ T, BadR P m n b T = 0 → ∀ r < T,
    isChild n (Nat.add (Nat.shiftLeft b 6) r) = true →
    Nat.land (fldW P (Nat.mul 22 r) 22) 1048575 < 64 * b + r ∧
      Nat.shiftRight (fldW P (Nat.mul 22 r) 22) 20 < m
  | 0, _, r, hr, _ => absurd hr (Nat.not_lt_zero r)
  | T + 1, h, r, hr, hch => by
    have h' : badStep P m n b T (BadR P m n b T) = 0 := h
    unfold badStep at h'
    have hsh : Nat.add (Nat.shiftLeft b 6) T = 64 * b + T := by rw [shl6]; rfl
    simp only [nIf_eq, bAnd_eq, blt_iff] at h'
    generalize hacc : BadR P m n b T = acc at h'
    have hz : acc = 0 ∧ (isChild n (Nat.add (Nat.shiftLeft b 6) T) = true →
        (Nat.land (fldW P (Nat.mul 22 T) 22) 1048575 < 64 * b + T ∧
          Nat.shiftRight (fldW P (Nat.mul 22 T) 22) 20 < m)) := by
      split_ifs at h' with hc hg
      · exact ⟨h', fun _ => by
          rw [Bool.and_eq_true, blt_iff, blt_iff, hsh] at hg
          exact hg⟩
      · exact ⟨h', fun hc' => absurd hc' hc⟩
    obtain ⟨hz0, hz1⟩ := hz
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hlt | rfl
    · exact BadR_spec P m n b T (hacc.trans hz0) r hlt hch
    · exact hz1 hch

private theorem getRec_lt (KX : ℕ → ℕ) (j : ℕ) : getRec KX 539 j < 2 ^ 539 := by
  rw [getRec_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem fldW_lt (r o w : ℕ) : fldW r o w < 2 ^ w := by
  rw [fldW_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem fldW_leaf (KX : ℕ → ℕ) (b r : ℕ) (hr : r < 64) :
    fldW (KX b) (Nat.mul 539 r) 539 = getRec KX 539 (64 * b + r) := by
  rw [getRec_eq, fldW_eq]
  have e1 : (64 * b + r) / 64 = b := by omega
  have e2 : (64 * b + r) % 64 = r := by omega
  rw [e1, e2, Nat.mul_comm r]
  rfl

theorem sLeaf_sound_of {C : SConsts} (hC : sConstsOK C = true)
    (hBlk : ∀ {r X K : ℕ}, r ≤ 64 → LCanon 11 r 49 X → LCanon 11 49 49 K →
      LCanon 11 r 49 (sBlk C X K) ∧ ∀ q < r, vec49 (sBlk C X K / 2 ^ (539 * q)) =
        Matrix.vecMul (vec49 (X / 2 ^ (539 * q))) (kM K))
    {KX PT : ℕ → ℕ} {Ks : List ℕ}
    {m n b r : ℕ} (hKs : ∀ s < m, LCanon 11 49 49 (pickL Ks s)) (h : sLeaf C KX PT Ks m n b = true)
    (hr : r < 64) (hi0 : 0 < 64 * b + r) (hin : 64 * b + r < n) :
    fldW (sRec PT (64 * b + r)) 0 20 < 64 * b + r ∧ fldW (sRec PT (64 * b + r)) 20 2 < m ∧
      ((∀ j < 64 * b + r, LCanon 11 1 49 (getRec KX 539 j)) →
        LCanon 11 1 49 (getRec KX 539 (64 * b + r)) ∧
        vec49 (getRec KX 539 (64 * b + r)) = Matrix.vecMul
          (vec49 (getRec KX 539 (fldW (sRec PT (64 * b + r)) 0 20)))
          (kM (pickL Ks (fldW (sRec PT (64 * b + r)) 20 2)))) := by
  have h' := h
  unfold sLeaf at h'
  rw [bAnd_eq, Bool.and_eq_true] at h'
  obtain ⟨hbad, hlab⟩ := h'
  have hbad0 : BadR (PT b) m n b 64 = 0 := by
    rw [← sBad_eq]
    exact beq_iff.1 hbad
  have hlab' := (recAnd_iff (fun s => Nat.beq (sBlk C (sGather KX PT n b s false) (pickL Ks s))
    (sGather KX PT n b s true)) m).1 hlab
  have hchild : isChild n (Nat.add (Nat.shiftLeft b 6) r) = true := (isChild_iff n b r).2 ⟨hi0, hin⟩
  obtain ⟨hpar, hlabm⟩ := BadR_spec (PT b) m n b 64 hbad0 r hr hchild
  have hsrec : sRec PT (64 * b + r) = fldW (PT b) (Nat.mul 22 r) 22 := by
    change getRec PT 22 (64 * b + r) = _
    rw [getRec_eq, fldW_eq]
    have e1 : (64 * b + r) / 64 = b := by omega
    have e2 : (64 * b + r) % 64 = r := by omega
    rw [e1, e2, Nat.mul_comm r]
    rfl
  have hfpar : fldW (sRec PT (64 * b + r)) 0 20 = Nat.land (fldW (PT b) (Nat.mul 22 r) 22) 1048575 := by
    rw [hsrec, fldW_eq, land20, Nat.pow_zero, Nat.div_one]
  have hflab : fldW (sRec PT (64 * b + r)) 20 2 = Nat.shiftRight (fldW (PT b) (Nat.mul 22 r) 22) 20 := by
    rw [hsrec, fldW_eq, shr20]
    refine Nat.mod_eq_of_lt ?_
    have h1 := fldW_lt (PT b) (Nat.mul 22 r) 22
    rw [show (2 : ℕ) ^ 2 = 4 from rfl]
    omega
  rw [hfpar, hflab]
  refine ⟨hpar, hlabm, fun hKXi => ?_⟩
  have hsm := hlabm
  have hcr : cF PT n b (Nat.shiftRight (fldW (PT b) (Nat.mul 22 r) 22) 20) r = true := by
    unfold cF
    rw [bAnd_eq, Bool.and_eq_true]
    exact ⟨hchild, beq_iff.2 rfl⟩
  have hEq := beq_iff.1 (hlab' _ hsm)
  rw [sGather_eq, sGather_eq] at hEq
  have hvF : ∀ r, vG KX PT b false r < 2 ^ 539 := fun r => getRec_lt KX _
  have hvT : ∀ r, vG KX PT b true r < 2 ^ 539 := fun r => fldW_lt _ _ _
  have hpar' : ∀ r', r' ≤ r → cF PT n b (Nat.shiftRight (fldW (PT b) (Nat.mul 22 r) 22) 20) r' = true →
      LCanon 11 1 49 (vG KX PT b false r') := by
    intro r' hr' hc'
    unfold cF at hc'
    rw [bAnd_eq, Bool.and_eq_true] at hc'
    obtain ⟨hch', -⟩ := hc'
    obtain ⟨hp1, -⟩ := BadR_spec (PT b) m n b 64 hbad0 r' (by omega) hch'
    exact hKXi (Nat.land (fldW (PT b) (Nat.mul 22 r') 22) 1048575) (by omega)
  obtain ⟨hcan1, hvec1⟩ := core hC hBlk hvF hvT (hKs _ hsm) hEq hr hcr hpar'
  have e1 : vG KX PT b true r = getRec KX 539 (64 * b + r) := fldW_leaf KX b r hr
  rw [e1] at hcan1 hvec1
  exact ⟨hcan1, hvec1⟩

end CFSG.KS.LyOm.SB6
end
