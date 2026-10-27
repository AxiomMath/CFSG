module

public import Certificates.Data.Kernel.Spor.PEnumR
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import Certificates.Data.Kernel.Spor.PEnumB
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.J2ModelsSound
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KS.PEnumR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem pg_div (w X j : Nat) : pg w (mask w) X j = X / 2 ^ (w * j) % 2 ^ w := by
  change (X >>> (w * j)) &&& mask w = _
  rw [PF.mask_eq, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem fld4 {w M4 : Nat} (hM : M4 = 2 ^ (4 * w) - 1) (X i k : Nat) (hk : k < 4) :
    Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight X (Nat.mul w i)) M4) (k * w)) (mask w) =
      pg w (mask w) X (i + k) := by
  subst hM
  rw [pg_div]
  change ((X >>> (w * i)) &&& (2 ^ (4 * w) - 1)) >>> (k * w) &&& mask w = _
  rw [PF.mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h4 : 2 ^ (4 * w) = 2 ^ (k * w) * 2 ^ ((4 - k) * w) := by
    rw [← Nat.pow_add, ← Nat.add_mul, Nat.add_sub_cancel' (by omega)]
  have hd : 2 ^ w ∣ 2 ^ ((4 - k) * w) :=
    Nat.pow_dvd_pow 2 (Nat.le_mul_of_pos_left w (by omega))
  rw [h4, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hd, Nat.div_div_eq_div_mul,
    ← Nat.pow_add, Nat.mul_add, Nat.mul_comm k w]

theorem hkGo4_succ {w M4 : Nat} (hM : M4 = 2 ^ (4 * w) - 1) (X q i h : Nat) :
    hkGo4 w (mask w) M4 X (q + 1) i h = hkGo4 w (mask w) M4 X q (i + 4)
      (hkStep (hkStep (hkStep (hkStep h (pg w (mask w) X i)) (pg w (mask w) X (i + 1)))
        (pg w (mask w) X (i + 2))) (pg w (mask w) X (i + 3))) := by
  have e0 := fld4 hM X i 0 (by omega)
  have e1 := fld4 hM X i 1 (by omega)
  have e2 := fld4 hM X i 2 (by omega)
  have e3 := fld4 hM X i 3 (by omega)
  have s0 : Nat.land (Nat.land (Nat.shiftRight X (Nat.mul w i)) M4) (mask w) =
      pg w (mask w) X i := by
    rw [Nat.zero_mul, Nat.add_zero] at e0
    exact e0
  have s1 : Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight X (Nat.mul w i)) M4) w)
      (mask w) = pg w (mask w) X (i + 1) := by
    rw [Nat.one_mul] at e1
    exact e1
  have s2 : Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight X (Nat.mul w i)) M4)
      (Nat.add w w)) (mask w) = pg w (mask w) X (i + 2) := by
    rw [show 2 * w = Nat.add w w by simp only [Nat.add_eq]; omega] at e2
    exact e2
  have s3 : Nat.land (Nat.shiftRight (Nat.land (Nat.shiftRight X (Nat.mul w i)) M4)
      (Nat.add w (Nat.add w w))) (mask w) = pg w (mask w) X (i + 3) := by
    rw [show 3 * w = Nat.add w (Nat.add w w) by simp only [Nat.add_eq]; omega] at e3
    exact e3
  change strictN (Nat.land (Nat.shiftRight X (Nat.mul w i)) M4) (fun c =>
      strictN (hkStep (hkStep (hkStep (hkStep h (Nat.land c (mask w)))
        (Nat.land (Nat.shiftRight c w) (mask w))) (Nat.land (Nat.shiftRight c (Nat.add w w)) (mask w)))
        (Nat.land (Nat.shiftRight c (Nat.add w (Nat.add w w))) (mask w))) (fun h' =>
      strictN (Nat.add i (nat_lit 4)) (fun i' => hkGo4 w (mask w) M4 X q i' h'))) = _
  rw [PF.strictN_eqP, PF.strictN_eqP, PF.strictN_eqP, s0, s1, s2, s3]

theorem hkGo_add4 (w m X r i h : Nat) :
    hkGo w m X (r + 4) i h = hkGo w m X r (i + 4)
      (hkStep (hkStep (hkStep (hkStep h (pg w m X i)) (pg w m X (i + 1)))
        (pg w m X (i + 2))) (pg w m X (i + 3))) := by
  rw [show r + 4 = r + 3 + 1 from rfl, hkGo_succ, show r + 3 = r + 2 + 1 from rfl, hkGo_succ,
    show r + 2 = r + 1 + 1 from rfl, hkGo_succ, hkGo_succ]

theorem hkGo4_eq {w M4 : Nat} (hM : M4 = 2 ^ (4 * w) - 1) (X : Nat) :
    ∀ q i h, hkGo4 w (mask w) M4 X q i h = hkGo w (mask w) X (4 * q) i h
  | 0, _, _ => rfl
  | q + 1, i, h => by
    rw [hkGo4_succ hM, hkGo4_eq hM X q, show 4 * (q + 1) = 4 * q + 4 by omega, hkGo_add4]

theorem hkey4_eq {n : Nat} (hn : n % 4 = 0) (w X : Nat) :
    hkey4 n w (mask w) X = hkeyK n w (mask w) X := by
  have hM : Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 4) w)) (nat_lit 1) =
      2 ^ (4 * w) - 1 := by
    change 1 <<< (4 * w) - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hq : 4 * Nat.shiftRight n (nat_lit 2) = n := by
    change 4 * (n >>> 2) = n
    rw [Nat.shiftRight_eq_div_pow]
    omega
  unfold hkey4 hkeyK
  rw [hkGo4_eq hM, hq]

theorem hvF_eq {n : Nat} (hn : n % 4 = 0) (w : Nat) (T HV : Nat → Nat) (i : Nat) :
    hvF n w (mask w) T HV i = CFSG.KS.PEnumB.hvK n w (mask w) T HV i := by
  unfold hvF CFSG.KS.PEnumB.hvK
  rw [hkey4_eq hn]

variable {n w : Nat}

theorem penumPtR_spec {m k cnt i : Nat} {GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtR n w m GI k cnt T PL POS SRT SRI i = true) :
    (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧
      r32 POS (parOf PL i * k + labOf PL i) = i) ∧
    (∀ j < k, r32 POS (i * k + j) < cnt ∧
      T (r32 POS (i * k + j)) = pcomp n w m (T i) (GI j)) := by
  unfold penumPtR at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨ht, hpos, -⟩ := h
  refine ⟨fun hi => ?_, fun j hj => ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at ht
    exact ⟨ht.1, ht.2.1, Nat.eq_of_beq_eq_true ht.2.2.1⟩
  · have hq := CFSG.KS.Raw.Orb.allN_iff.1 hpos j hj
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Nat.mul_eq, Nat.add_eq,
      Bool.and_eq_true, Nat.blt_eq] at hq
    exact ⟨hq.1, Nat.eq_of_beq_eq_true hq.2.1⟩

theorem head_zero {cnt cap : Nat} {T PL : Nat → Nat}
    (hh : penumHdK (pidn n w) cnt cap T PL = true) : T 0 = pidn n w := by
  unfold penumHdK at hh
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact Nat.eq_of_beq_eq_true hh.2.2.1

theorem penumR_step {k cnt i : Nat} {GI T PL POS SRT SRI : Nat → Nat}
    (hb : ∀ i < cnt, penumPtR n w (mask w) GI k cnt T PL POS SRT SRI i = true) (hi : i < cnt)
    (hi0 : i ≠ 0) :
    parOf PL i < i ∧ labOf PL i < k ∧
      T i = pcomp n w (mask w) (T (parOf PL i)) (GI (labOf PL i)) := by
  obtain ⟨hp, hl, e⟩ := (penumPtR_spec (hb i hi)).1 hi0
  obtain ⟨-, e'⟩ := (penumPtR_spec (hb (parOf PL i) (by omega))).2 _ hl
  rw [e] at e'
  exact ⟨hp, hl, e'⟩

theorem penumR_canon {k cnt cap : Nat} {GI T PL POS SRT SRI : Nat → Nat}
    (hsz : szOK n w = true) (hGI : ∀ j < k, canonK n w (mask w) (n * w) (GI j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtR n w (mask w) GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [head_zero hh]
      exact (CFSG.KC.BfsPin.PP.id hsz).1
    · obtain ⟨hp, hl, e⟩ := penumR_step hb hi hi0
      rw [e]
      exact CFSG.KC.BfsPin.canonK_pcomp (ih _ hp (by omega)) (hGI _ hl)

theorem penumPtK_of_R {k cnt cap : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hsz : szOK n w = true) (hGI : ∀ j < k, canonK n w (mask w) (n * w) (GI j) = true)
    (hG : ∀ j < k, G j = pidn n w) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtR n w (mask w) GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true := by
  have hT := penumR_canon hsz hGI hh hb
  have hstep : ∀ j < k, ∀ x < cnt,
      stepK n w (mask w) true G GI j (T x) = pcomp n w (mask w) (T x) (GI j) := by
    intro j hj x hx
    have e0 : stepK n w (mask w) true G GI j (T x) =
        pcomp n w (mask w) (pcomp n w (mask w) (G j) (T x)) (GI j) := rfl
    rw [e0, hG _ hj, CFSG.KC.J2Models.pcomp_idL (hT x hx)]
  intro i hi
  have h := hb i hi
  unfold penumPtR at h
  unfold penumPtK
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hT i hi, ?_, ?_, h3⟩
  · by_cases hi0 : i = 0
    · subst hi0
      rfl
    · obtain ⟨hp, hl, e⟩ := penumR_step hb hi hi0
      have hpos := ((penumPtR_spec (hb i hi)).1 hi0).2.2
      have e1 : Nat.beq (r32 POS (Nat.add (Nat.mul (parOf PL i) k) (labOf PL i))) i = true := by
        simp only [Nat.mul_eq, Nat.add_eq]
        rw [hpos, Nat.beq_refl]
      have e2 : Nat.beq (T i) (stepK n w (mask w) true G GI (labOf PL i) (T (parOf PL i))) =
          true := by
        rw [hstep _ hl _ (by omega), ← e, Nat.beq_refl]
      rw [e1] at h1
      rw [e2]
      exact h1
  · rw [CFSG.KS.Raw.Orb.allN_iff] at h2 ⊢
    intro j hj
    have hq := h2 j hj
    rw [hstep _ hj _ hi]
    exact hq

end CFSG.KS.PEnumR

end
