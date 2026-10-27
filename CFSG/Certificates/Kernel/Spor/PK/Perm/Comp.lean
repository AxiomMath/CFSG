module

public import CFSG.Certificates.Kernel.Spor.PK.Enc

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS

private theorem lor_enc {w a b : Nat} {f : Nat → Nat} (hf : ∀ i < a, f i < 2 ^ w) :
    Nat.lor (enc w f a) (Nat.shiftLeft (enc w (fun i => f (a + i)) b) (w * a)) =
      enc w f (a + b) := by
  rw [enc_add]
  exact lor_shiftLeft_eq_add (enc_lt hf)

private theorem two_pow_double (k : Nat) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_two]

private theorem leafv (w p q x : Nat) :
    fld(p, Nat.mul w fld(q, Nat.mul w x, mask w), mask w) = fd w p (fd w q x) := by
  rw [fld_eq, fld_eq]
  rfl

theorem pmkH_eq (w p q d lo : Nat) :
    pmkH w (mask w) p q d lo = enc w (fun i => fd w p (fd w q (lo + i))) (2 ^ d) := by
  induction d generalizing lo with
  | zero =>
    show fld(p, Nat.mul w fld(q, Nat.mul w lo, mask w), mask w) = _
    rw [leafv]
    simp [enc]
  | succ d ih =>
    show Nat.lor (pmkH w (mask w) p q d lo)
      (Nat.shiftLeft (pmkH w (mask w) p q d (Nat.add lo (Nat.shiftLeft 1 d)))
        (Nat.mul w (Nat.shiftLeft 1 d))) = _
    have h1 : Nat.shiftLeft 1 d = 2 ^ d := by simp [Nat.shiftLeft_eq]
    rw [ih, ih, h1, Nat.add_eq, Nat.mul_eq, two_pow_double]
    have := lor_enc (w := w) (a := 2 ^ d) (b := 2 ^ d)
      (f := fun i => fd w p (fd w q (lo + i))) (fun i _ => fd_lt _ _ _)
    simpa only [Nat.add_assoc] using this

private theorem lor2 {w : Nat} {f : Nat → Nat} (h0 : f 0 < 2 ^ w) :
    Nat.lor (f 0) (Nat.shiftLeft (f 1) w) = enc w f 2 := by
  have h := lor_shiftLeft_eq_add (y := f 1) h0
  have e : enc w f 2 = f 0 + f 1 * 2 ^ w := by simp [enc]
  rw [e]
  exact h

private theorem lor4 {w : Nat} {f : Nat → Nat} (hf : ∀ i < 4, f i < 2 ^ w) :
    Nat.lor (Nat.lor (f 0) (Nat.shiftLeft (f 1) w))
      (Nat.shiftLeft (Nat.lor (f 2) (Nat.shiftLeft (f 3) w)) (Nat.mul w 2)) = enc w f 4 := by
  have h := lor_enc (w := w) (a := 2) (b := 2) (f := f) (fun i hi => hf i (by omega))
  rw [lor2 (hf 0 (by omega)), Nat.mul_eq]
  have h2 : Nat.lor (f 2) (Nat.shiftLeft (f 3) w) = enc w (fun i => f (2 + i)) 2 :=
    lor2 (f := fun i => f (2 + i)) (hf 2 (by omega))
  rw [h2]
  exact h

private theorem lor8 {w : Nat} {f : Nat → Nat} (hf : ∀ i < 8, f i < 2 ^ w) :
    Nat.lor
      (Nat.lor (Nat.lor (f 0) (Nat.shiftLeft (f 1) w))
        (Nat.shiftLeft (Nat.lor (f 2) (Nat.shiftLeft (f 3) w)) (Nat.mul w 2)))
      (Nat.shiftLeft
        (Nat.lor (Nat.lor (f 4) (Nat.shiftLeft (f 5) w))
          (Nat.shiftLeft (Nat.lor (f 6) (Nat.shiftLeft (f 7) w)) (Nat.mul w 2)))
        (Nat.mul w 4)) = enc w f 8 := by
  have h := lor_enc (w := w) (a := 4) (b := 4) (f := f) (fun i hi => hf i (by omega))
  rw [lor4 (fun i hi => hf i (by omega))]
  have h2 : Nat.lor (Nat.lor (f 4) (Nat.shiftLeft (f 5) w))
          (Nat.shiftLeft (Nat.lor (f 6) (Nat.shiftLeft (f 7) w)) (Nat.mul w 2)) =
      enc w (fun i => f (4 + i)) 4 :=
    lor4 (f := fun i => f (4 + i)) (fun i hi => hf (4 + i) (by omega))
  rw [h2, Nat.mul_eq]
  exact h

theorem pmkH8_eq (w p q d lo : Nat) :
    pmkH8 w (mask w) p q d lo = enc w (fun i => fd w p (fd w q (lo + i))) (2 ^ (d + 3)) := by
  induction d generalizing lo with
  | zero =>
    refine Eq.trans ?_ (lor8 (w := w) (f := fun i => fd w p (fd w q (lo + i)))
      (fun i _ => fd_lt _ _ _))
    dsimp only [pmkH8]
    simp only [leafv]
    rfl
  | succ d ih =>
    show Nat.lor (pmkH8 w (mask w) p q d lo)
      (Nat.shiftLeft (pmkH8 w (mask w) p q d (Nat.add lo (Nat.shiftLeft 8 d)))
        (Nat.mul w (Nat.shiftLeft 8 d))) = _
    have h1 : Nat.shiftLeft 8 d = 2 ^ (d + 3) := by
      show 8 <<< d = _
      rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm]
    have h3 : 2 ^ (d + 1 + 3) = 2 ^ (d + 3) + 2 ^ (d + 3) := by
      rw [show d + 1 + 3 = (d + 3) + 1 by omega, two_pow_double]
    rw [ih, ih, h1, Nat.add_eq, Nat.mul_eq, h3]
    have := lor_enc (w := w) (a := 2 ^ (d + 3)) (b := 2 ^ (d + 3))
      (f := fun i => fd w p (fd w q (lo + i))) (fun i _ => fd_lt _ _ _)
    simpa only [Nat.add_assoc] using this

private noncomputable def pcR (n w m p q : Nat) (K : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih b rem => nIf(Nat.beq rem (nat_lit 0), nat_lit 0,
      nIf(Nat.beq (Nat.land rem (nat_lit 1)) (nat_lit 0),
        ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)),
        strictN (Nat.sub n (Nat.shiftLeft rem b)) (fun lo =>
          Nat.lor
            (Nat.shiftLeft
              (nIf(Nat.blt b (nat_lit 3), pmkH w m p q b lo,
                pmkH8 w m p q (Nat.sub b (nat_lit 3)) lo))
              (Nat.mul w lo))
            (ih (Nat.succ b) (Nat.shiftRight rem (nat_lit 1)))))))
    K

private theorem pcomp_def (n w m p q : Nat) : pcomp n w m p q = pcR n w m p q 32 0 n := rfl

private theorem pcR_zero (n w m p q b rem : Nat) : pcR n w m p q 0 b rem = 0 := rfl

private theorem pcR_succ (n w p q K b rem : Nat) :
    pcR n w (mask w) p q (K + 1) b rem =
      if rem = 0 then 0 else
      if rem % 2 = 0 then pcR n w (mask w) p q K (b + 1) (rem / 2) else
      ((if b < 3 then pmkH w (mask w) p q b (n - rem * 2 ^ b)
          else pmkH8 w (mask w) p q (b - 3) (n - rem * 2 ^ b)) * 2 ^ (w * (n - rem * 2 ^ b))) |||
        pcR n w (mask w) p q K (b + 1) (rem / 2) := by
  simp only [pcR, nIf_eq, strictN_eq, Nat.beq_eq, Nat.blt_eq, Nat.land_eq, Nat.lor_eq,
    Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.and_one_is_mod, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.sub_eq, Nat.mul_eq, Nat.succ_eq_add_one, Nat.pow_one]

private theorem pcR_spec (n w p q : Nat) (K : Nat) : ∀ b, n < 2 ^ (b + K) →
    pcR n w (mask w) p q K b (n / 2 ^ b) + enc w (fun i => fd w p (fd w q i)) (n % 2 ^ b) =
        enc w (fun i => fd w p (fd w q i)) n ∧
      2 ^ (w * (n % 2 ^ b)) ∣ pcR n w (mask w) p q K b (n / 2 ^ b) := by
  induction K with
  | zero =>
    intro b hb
    have hlt : n < 2 ^ b := by simpa using hb
    rw [pcR_zero, Nat.mod_eq_of_lt hlt]
    exact ⟨Nat.zero_add _, Nat.dvd_zero _⟩
  | succ K ih =>
    intro b hb
    rw [pcR_succ]
    by_cases h0 : n / 2 ^ b = 0
    · have hlt : n < 2 ^ b := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos b)).1 h0
      rw [if_pos h0, Nat.mod_eq_of_lt hlt]
      exact ⟨Nat.zero_add _, Nat.dvd_zero _⟩
    · rw [if_neg h0]
      have hdiv : n / 2 ^ b / 2 = n / 2 ^ (b + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      have hmod : n % 2 ^ (b + 1) = n % 2 ^ b + 2 ^ b * (n / 2 ^ b % 2) := Nat.mod_pow_succ
      have hb' : n < 2 ^ (b + 1 + K) := by rwa [show b + 1 + K = b + (K + 1) by omega]
      obtain ⟨ih1, ih2⟩ := ih (b + 1) hb'
      rw [hdiv]
      by_cases h1 : n / 2 ^ b % 2 = 0
      · rw [if_pos h1]
        rw [h1, Nat.mul_zero, Nat.add_zero] at hmod
        rw [hmod] at ih1 ih2
        exact ⟨ih1, ih2⟩
      · rw [if_neg h1]
        have h1' : n / 2 ^ b % 2 = 1 := by omega
        have hlo : n - n / 2 ^ b * 2 ^ b = n % 2 ^ b := by
          have := @Nat.div_mul_self_eq_mod_sub_self n (2 ^ b)
          have := Nat.mod_le n (2 ^ b)
          omega
        rw [hlo]
        have hmod' : n % 2 ^ (b + 1) = n % 2 ^ b + 2 ^ b := by rw [hmod, h1', Nat.mul_one]
        rw [hmod'] at ih1 ih2
        generalize hlo' : n % 2 ^ b = lo at *
        have hA : (if b < 3 then pmkH w (mask w) p q b lo else pmkH8 w (mask w) p q (b - 3) lo) =
            enc w (fun i => fd w p (fd w q (lo + i))) (2 ^ b) := by
          by_cases h3 : b < 3
          · rw [if_pos h3]
            exact pmkH_eq w p q b lo
          · rw [if_neg h3]
            have := pmkH8_eq w p q (b - 3) lo
            rwa [show b - 3 + 3 = b by omega] at this
        rw [hA]
        have hAlt : enc w (fun i => fd w p (fd w q (lo + i))) (2 ^ b) < 2 ^ (w * 2 ^ b) :=
          enc_lt (fun i _ => fd_lt _ _ _)
        have hlt : enc w (fun i => fd w p (fd w q (lo + i))) (2 ^ b) * 2 ^ (w * lo) <
            2 ^ (w * (lo + 2 ^ b)) := by
          calc enc w (fun i => fd w p (fd w q (lo + i))) (2 ^ b) * 2 ^ (w * lo)
              < 2 ^ (w * 2 ^ b) * 2 ^ (w * lo) :=
                Nat.mul_lt_mul_of_pos_right hAlt (Nat.two_pow_pos _)
            _ = 2 ^ (w * (lo + 2 ^ b)) := by
                rw [← Nat.pow_add, Nat.mul_add, Nat.add_comm]
        rw [lor_eq_add_of_lt_of_dvd hlt ih2]
        refine ⟨?_, ?_⟩
        · rw [enc_add] at ih1
          omega
        · exact Nat.dvd_add (Nat.dvd_mul_left _ _)
            (Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left w (Nat.le_add_right lo _))) ih2)

theorem pcomp_eq {n : Nat} (hn : n < 2 ^ 32) (w p q : Nat) :
    pcomp n w (mask w) p q = enc w (fun i => fd w p (fd w q i)) n := by
  rw [pcomp_def]
  have h := (pcR_spec n w p q 32 0 (by simpa using hn)).1
  simpa [enc, Nat.mod_one] using h

theorem pcomp_lt {n : Nat} (hn : n < 2 ^ 32) (w p q : Nat) :
    pcomp n w (mask w) p q < 2 ^ (w * n) := by
  rw [pcomp_eq hn]
  exact enc_lt (fun i _ => fd_lt _ _ _)

theorem fd_pcomp {n : Nat} (hn : n < 2 ^ 32) (w p q : Nat) {i : Nat} (hi : i < n) :
    fd w (pcomp n w (mask w) p q) i = fd w p (fd w q i) := by
  rw [pcomp_eq hn]
  exact fd_enc (fun i _ => fd_lt _ _ _) hi

end CFSG.KS.PK

end
