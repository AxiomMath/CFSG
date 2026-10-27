module

public import CFSG.Certificates.Kernel.J4.ModelsSound
public import CFSG.Certificates.Kernel.DceTwWalk
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KJ4.KRoute

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KC.Loop
open CFSG.Certificates.DceTw (RelT)
open CFSG.Certificates.DceWord (lvE)
open CFSG.Certificates.J4Words (jv)
open CFSG.Certificates.J4KShape (rv)

set_option exponentiation.threshold 400

theorem lor_shl {a n : ℕ} (b : ℕ) (ha : a < 2 ^ n) : a ||| b <<< n = a + 2 ^ n * b := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm]

theorem divA {a n : ℕ} (R : ℕ) (ha : a < 2 ^ n) : (a + 2 ^ n * R) / 2 ^ n = R := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem modA {a n : ℕ} (R : ℕ) (ha : a < 2 ^ n) : (a + 2 ^ n * R) % 2 ^ n = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem div32 (X : ℕ) : X / 2 ^ 32 = X / 2 ^ 16 / 2 ^ 16 := by
  rw [Nat.div_div_eq_div_mul]
  norm_num

theorem div64 (X : ℕ) : X / 2 ^ 64 = X / 2 ^ 16 / 2 ^ 16 / 2 ^ 32 := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  norm_num

theorem div96 (X : ℕ) : X / 2 ^ 96 = X / 2 ^ 16 / 2 ^ 16 / 2 ^ 32 / 2 ^ 32 := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  norm_num

theorem cIdx_eq (x : ℕ) : cIdx x = x % 2 ^ 32 := by
  change x &&& (2 ^ 32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem cNd_eq (x : ℕ) : cNd x = x / 2 ^ 32 % 2 ^ 32 := by
  change (x >>> 32) &&& (2 ^ 32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem mkC_eq {k : ℕ} (nd : ℕ) (hk : k < 2 ^ 32) : mkC k nd = k + 2 ^ 32 * nd := by
  change k ||| nd <<< 32 = _
  exact lor_shl nd hk

theorem cIdx_mkC {k nd : ℕ} (hk : k < 2 ^ 32) : cIdx (mkC k nd) = k := by
  rw [cIdx_eq, mkC_eq nd hk]
  omega

theorem cNd_mkC {k nd : ℕ} (hk : k < 2 ^ 32) (hn : nd < 2 ^ 32) : cNd (mkC k nd) = nd := by
  rw [cNd_eq, mkC_eq nd hk]
  omega

theorem cIdx_FAIL : cIdx FAIL = 2 ^ 31 := by
  rw [cIdx_eq]
  rfl

theorem dD_eq (d : ℕ) : dD d = d % 2 ^ 16 := by
  change d &&& (2 ^ 16 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem dD0_eq (d : ℕ) : dD0 d = d / 2 ^ 16 % 2 ^ 16 := by
  change (d >>> 16) &&& (2 ^ 16 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem dK_eq (d : ℕ) : dK d = d / 2 ^ 32 % 2 ^ 32 := by
  change (d >>> 32) &&& (2 ^ 32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem dNd_eq (d : ℕ) : dNd d = d / 2 ^ 64 % 2 ^ 32 := by
  change (d >>> 64) &&& (2 ^ 32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem dP0_eq (d : ℕ) : dP0 d = d / 2 ^ 96 := by
  change d >>> 96 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem mkD_eq {D0 K nd : ℕ} (P0 : ℕ) (h0 : D0 < 2 ^ 16) (hK : K < 2 ^ 32) (hn : nd < 2 ^ 32) :
    mkD D0 K nd P0 = D0 + 2 ^ 16 * (D0 + 2 ^ 16 * (K + 2 ^ 32 * (nd + 2 ^ 32 * P0))) := by
  change D0 ||| (D0 <<< 16 ||| (K <<< 32 ||| (nd <<< 64 ||| P0 <<< 96))) = _
  have a1 : nd <<< 64 ||| P0 <<< 96 = (nd + 2 ^ 32 * P0) <<< 64 := by
    rw [← lor_shl P0 hn, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add]
  have a2 : K <<< 32 ||| (nd + 2 ^ 32 * P0) <<< 64 = (K + 2 ^ 32 * (nd + 2 ^ 32 * P0)) <<< 32 := by
    rw [← lor_shl _ hK, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add]
  have a3 : D0 <<< 16 ||| (K + 2 ^ 32 * (nd + 2 ^ 32 * P0)) <<< 32 =
      (D0 + 2 ^ 16 * (K + 2 ^ 32 * (nd + 2 ^ 32 * P0))) <<< 16 := by
    rw [← lor_shl _ h0, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add]
  rw [a1, a2, a3, lor_shl _ h0]

theorem setD_eq (d : ℕ) {D : ℕ} (hD : D < 2 ^ 16) : setD d D = D + 2 ^ 16 * (d / 2 ^ 16) := by
  change (d >>> 16) <<< 16 ||| D = _
  rw [Nat.or_comm, lor_shl _ hD, Nat.shiftRight_eq_div_pow]

section mkD

variable {D0 K nd : ℕ} (P0 : ℕ) (h0 : D0 < 2 ^ 16) (hK : K < 2 ^ 32) (hn : nd < 2 ^ 32)
include h0 hK hn

theorem dD_mkD : dD (mkD D0 K nd P0) = D0 := by
  rw [dD_eq, mkD_eq P0 h0 hK hn, modA _ h0]

theorem dD0_mkD : dD0 (mkD D0 K nd P0) = D0 := by
  rw [dD0_eq, mkD_eq P0 h0 hK hn, divA _ h0, modA _ h0]

theorem dK_mkD : dK (mkD D0 K nd P0) = K := by
  rw [dK_eq, mkD_eq P0 h0 hK hn, div32, divA _ h0, divA _ h0, modA _ hK]

theorem dNd_mkD : dNd (mkD D0 K nd P0) = nd := by
  rw [dNd_eq, mkD_eq P0 h0 hK hn, div64, divA _ h0, divA _ h0, divA _ hK, modA _ hn]

theorem dP0_mkD : dP0 (mkD D0 K nd P0) = P0 := by
  rw [dP0_eq, mkD_eq P0 h0 hK hn, div96, divA _ h0, divA _ h0, divA _ hK, divA _ hn]

end mkD

section setD

variable (d : ℕ) {D : ℕ} (hD : D < 2 ^ 16)
include hD

theorem dD_setD : dD (setD d D) = D := by
  rw [dD_eq, setD_eq d hD, modA _ hD]

theorem dD0_setD : dD0 (setD d D) = dD0 d := by
  rw [dD0_eq, dD0_eq, setD_eq d hD, divA _ hD]

theorem dK_setD : dK (setD d D) = dK d := by
  rw [dK_eq, dK_eq, setD_eq d hD, div32, div32 d, divA _ hD]

theorem dNd_setD : dNd (setD d D) = dNd d := by
  rw [dNd_eq, dNd_eq, setD_eq d hD, div64, div64 d, divA _ hD]

theorem dP0_setD : dP0 (setD d D) = dP0 d := by
  rw [dP0_eq, dP0_eq, setD_eq d hD, div96, div96 d, divA _ hD]

end setD

theorem lt16_of_land {x : ℕ} (y : ℕ) (h : x = Nat.land y (nat_lit 65535)) : x < 2 ^ 16 := by
  rw [h]
  exact Nat.and_lt_two_pow _ (by decide)

theorem fD_lt (F : ℕ) : fD F < 2 ^ 16 := lt16_of_land _ rfl
theorem fDp_lt (F : ℕ) : fDp F < 2 ^ 16 := lt16_of_land _ rfl
theorem f16_lt (p o : ℕ) : f16 p o < 2 ^ 16 := lt16_of_land _ rfl

theorem fIdx_lt (F : ℕ) : fIdx F < 2 ^ 20 := Nat.and_lt_two_pow _ (by decide)

theorem cIdx_lt (x : ℕ) : cIdx x < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)
theorem cNd_lt (x : ℕ) : cNd x < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)
theorem dK_lt (d : ℕ) : dK d < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)
theorem dNd_lt (d : ℕ) : dNd d < 2 ^ 32 := Nat.and_lt_two_pow _ (by decide)

theorem letAt_eq (c : ℕ) : letAt c = c / 2 % 256 := by
  change (c >>> 1) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem adv0_eq (c : ℕ) : adv c 1 0 = c % 2 + 2 * (c / 512) := by
  change (c &&& 1 ||| 0) ||| (c >>> 9) <<< 1 = _
  rw [Nat.or_zero, Nat.and_one_is_mod, lor_shl _ (by omega : c % 2 < 2 ^ 1),
    Nat.shiftRight_eq_div_pow]
  norm_num

theorem adv1_eq (c : ℕ) : adv c 1 1 = 1 + 2 * (c / 512) := by
  change (c &&& 1 ||| 1) ||| (c >>> 9) <<< 1 = _
  have e : c &&& 1 ||| 1 = 1 := by
    rw [Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> rfl
  rw [e, lor_shl _ (by norm_num : (1 : ℕ) < 2 ^ 1), Nat.shiftRight_eq_div_pow]
  rfl

theorem two_pow_eight_mul (n : ℕ) : (2 : ℕ) ^ (8 * n) = 256 ^ n := by
  rw [pow_mul]
  norm_num

theorem wInit_eq {W n : ℕ} (hW : W < 256 ^ n) : wInit W n = 2 * (W + 256 ^ n * 254) := by
  change (W ||| 254 <<< (8 * n)) <<< 1 = _
  rw [lor_shl _ (by rwa [two_pow_eight_mul]), two_pow_eight_mul, Nat.shiftLeft_eq, pow_one,
    Nat.mul_comm, Nat.mul_comm (256 ^ n)]

theorem wLet_eq (W i : ℕ) : wLet W i = W / 256 ^ i % 256 := by
  change (W >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, two_pow_eight_mul]

theorem wFits_lt {W n : ℕ} (h : wFits W n = true) : W < 256 ^ n := by
  have h' : W < 1 <<< (8 * n) := blt_eq_true.1 h
  rwa [Nat.one_shiftLeft, two_pow_eight_mul] at h'

@[expose] def Cur (c W n i : ℕ) : Prop := c / 2 = (W + 256 ^ n * 254) / 256 ^ i

theorem cur_split (W i m : ℕ) :
    (W + 256 ^ (i + 1 + m) * 254) / 256 ^ i = W / 256 ^ i + 256 * (256 ^ m * 254) := by
  have e : 256 ^ (i + 1 + m) * 254 = 256 ^ i * (256 * (256 ^ m * 254)) := by
    rw [pow_add, pow_succ]
    ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity)]

theorem cur_letter {c W n i : ℕ} (hW : W < 256 ^ n) (hin : i ≤ n) (hc : Cur c W n i)
    (hl : letAt c ≠ 254) : i < n ∧ letAt c = wLet W i := by
  rw [letAt_eq, hc] at hl ⊢
  rcases Nat.lt_or_ge i n with h | h
  · refine ⟨h, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = i + 1 + m := ⟨n - i - 1, by omega⟩
    rw [cur_split, Nat.add_mul_mod_self_left, wLet_eq]
  · exfalso
    have e : i = n := by omega
    subst e
    apply hl
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hW]

theorem cur_adv {c W n i S : ℕ} (hS : S < 2) (hc : Cur c W n i) :
    Cur (adv c 1 S) W n (i + 1) := by
  unfold Cur at *
  have e : adv c 1 S / 2 = c / 2 / 256 := by
    rcases (by omega : S = 0 ∨ S = 1) with rfl | rfl
    · rw [adv0_eq]
      omega
    · rw [adv1_eq]
      omega
  rw [e, hc, Nat.div_div_eq_div_mul, pow_succ]

theorem adv_mod0 (c : ℕ) : adv c 1 0 % 2 = c % 2 := by
  rw [adv0_eq]
  omega

theorem adv_mod1 (c : ℕ) : adv c 1 1 % 2 = 1 := by
  rw [adv1_eq]
  omega

theorem cur_end {W n i : ℕ} (hin : i ≤ n) (hc : Cur 509 W n i) : i = n := by
  unfold Cur at hc
  by_contra hne
  obtain ⟨m, rfl⟩ : ∃ m, n = i + 1 + m := ⟨n - i - 1, by omega⟩
  rw [cur_split] at hc
  have : 0 < 256 ^ m := by positivity
  generalize W / 256 ^ i = A at hc
  omega

theorem cur_init {W n : ℕ} (hW : W < 256 ^ n) : Cur (wInit W n) W n 0 := by
  unfold Cur
  rw [wInit_eq hW, pow_zero, Nat.div_one]
  omega

theorem wInit_mod {W n : ℕ} (hW : W < 256 ^ n) : wInit W n % 2 = 0 := by
  rw [wInit_eq hW]
  omega

theorem strictT_eq {α : Type} (y : ℕ) (k : ℕ → α) : strictT y k = k y := by
  cases y <;> rfl

theorem forceK_eq {α : Type} (q : ℕ × St) (f : ℕ × St → α) : forceK q f = f q := by
  obtain ⟨m, d, p, c⟩ := q
  simp only [forceK, strictT_eq]

theorem brec_cases {α : Type} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = a ∨
      (c = true ∧ Bool.rec (motive := fun _ => α) a b c = b) := by
  cases c
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩

theorem recOK_spec {F k ND NOM : ℕ} (h : recOK F k ND NOM = true) :
    fIdx F = k ∧ fD F < ND ∧ fDp F < ND ∧ fJ F ≤ NOM ∧ mul12 (fPi F) (fPiI F) = ident12 := by
  unfold recOK at h
  simp only [andB_eq_true, beq_eq_true, blt_eq_true, Nat.ble_eq, mulF_eq] at h
  exact h

theorem refS_spec {K S g c : ℕ} (h : refS K S g c = true) :
    (S = 1 ∧ g = K ∧ c % 2 = 0) ∨ (S ≠ 1 ∧ g < K) := by
  unfold refS at h
  cases hS : Nat.beq S 1
  · simp only [hS] at h
    exact Or.inr ⟨Nat.ne_of_beq_eq_false hS, blt_eq_true.1 h⟩
  · simp only [hS, andB_eq_true, beq_eq_true] at h
    refine Or.inl ⟨Nat.eq_of_beq_eq_true hS, h.1, ?_⟩
    have h2 : c &&& 1 = 0 := h.2
    rwa [Nat.and_one_is_mod] at h2

theorem sNs_spec (LET d p c : ℕ) :
    sNs LET (d, (p, c)) = bad ∨
      (letAt c < 4 ∧ sNs LET (d, (p, c)) = (d, (mul12 p (letMat LET (letAt c)), adv c 1 0))) := by
  dsimp only [sNs]
  exact (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ⟨blt_eq_true.1 hb, h⟩

theorem sEfs_spec (FT : ℕ → ℕ) (S g d p c : ℕ) :
    sEfs FT S g (d, (p, c)) = bad ∨
      (letAt c = 255 ∧ refS (dK d) S g c = true ∧ dD d = fD (FT g) ∧ fJ (FT g) = 0 ∧
        sEfs FT S g (d, (p, c)) = (setD d (fDp (FT g)), (mul12 (fPi (FT g)) p, adv c 1 S))) := by
  dsimp only [sEfs]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [andB_eq_true, beq_eq_true] at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  exact ⟨h1, h2, h3, h4, by rw [h, mulF_eq]⟩

theorem sEbs_spec (FT : ℕ → ℕ) (S g d p c : ℕ) :
    sEbs FT S g (d, (p, c)) = bad ∨
      (letAt c = 255 ∧ refS (dK d) S g c = true ∧ dD d = fDp (FT g) ∧ fJ (FT g) = 0 ∧
        sEbs FT S g (d, (p, c)) = (setD d (fD (FT g)), (mul12 (fPiI (FT g)) p, adv c 1 S))) := by
  dsimp only [sEbs]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [andB_eq_true, beq_eq_true] at hb
  obtain ⟨h1, h2, h3, h4⟩ := hb
  exact ⟨h1, h2, h3, h4, by rw [h, mulF_eq]⟩

theorem sUfs_spec (FT OT LT : ℕ → ℕ) (TH S g e h TAU d p c : ℕ) :
    sUfs FT OT LT TH S g e h TAU (d, (p, c)) = bad ∨
      (letAt c = 4 ∧ refS (dK d) S g c = true ∧ dD d = fD (FT g) ∧ 0 < fJ (FT g) ∧
        oJ (OT (fJ (FT g) - 1)) = fJ (FT g) ∧ e < 512 ∧ TAU = mul12 (oG (OT (fJ (FT g) - 1))) p ∧
        inT TH (lamT (LT e)) h TAU = true ∧
        sUfs FT OT LT TH S g e h TAU (d, (p, c)) = (setD d (fDp (FT g)),
          (mul12 (mul12 (fPi (FT g)) (oGi' (OT (fJ (FT g) - 1))))
            (mul12 (lP' (LT e)) (Nat.land TAU linMask)), adv c 1 S))) := by
  dsimp only [sUfs]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [andB_eq_true, beq_eq_true, blt_eq_true, mulF_eq] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by rw [h]; simp only [mulF_eq]; rfl⟩

theorem sUbs_spec (FT OT LT : ℕ → ℕ) (TH S g e h RHO d p c : ℕ) :
    sUbs FT OT LT TH S g e h RHO (d, (p, c)) = bad ∨
      (letAt c = 4 ∧ refS (dK d) S g c = true ∧ dD d = fDp (FT g) ∧ 0 < fJ (FT g) ∧
        oJ (OT (fJ (FT g) - 1)) = fJ (FT g) ∧ e < 512 ∧
        RHO = mul12 (mul12 (oG (OT (fJ (FT g) - 1))) (fPiI (FT g))) p ∧
        inT TH (lamT (LT e)) h RHO = true ∧
        sUbs FT OT LT TH S g e h RHO (d, (p, c)) = (setD d (fD (FT g)),
          (mul12 (oGi' (OT (fJ (FT g) - 1))) (mul12 (lP' (LT e)) (Nat.land RHO linMask)),
            adv c 1 S))) := by
  dsimp only [sUbs]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [andB_eq_true, beq_eq_true, blt_eq_true, mulF_eq] at hb
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by rw [h]; simp only [mulF_eq]; rfl⟩

theorem stS_spec (FT HT WT : ℕ → ℕ) (ND NOM a b D0 w st : ℕ) :
    stS FT HT WT ND NOM a b D0 w st = bad ∨
      (0 < HT a ∧ 0 < HT b ∧ D0 < ND ∧ recOK (FT (cIdx st)) (cIdx st) ND NOM = true ∧
        stS FT HT WT ND NOM a b D0 w st =
          (mkD D0 (cIdx st) (cNd st) (mul12 (hInv (HT a)) (hMat (HT b))),
            (mul12 (hInv (HT a)) (hMat (HT b)), wInit (wW (WT w)) (wN (WT w))))) := by
  simp only [stS, strictT_eq, mulF_eq]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [hdrIn, andB_eq_true, blt_eq_true] at hb
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hb
  exact ⟨h1, h2, h3, h4, h⟩

theorem jTree_spec (FT : ℕ → ℕ) (ND NOM st : ℕ) :
    jTree FT false ND NOM st = FAIL ∨
      (recOK (FT (cIdx st)) (cIdx st) ND NOM = true ∧ 0 < fJ (FT (cIdx st)) ∧
        fDp (FT (cIdx st)) = cNd st ∧ fD (FT (cIdx st)) < cNd st ∧ fPi (FT (cIdx st)) = ident12 ∧
        jTree FT false ND NOM st = mkC (cIdx st + 1) (cNd st + 1)) := by
  simp only [jTree, strictN_eq]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [andB_eq_true, beq_eq_true, blt_eq_true] at hb
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h⟩

theorem jAx_spec (FT HT : ℕ → ℕ) (ND NOM a b st : ℕ) :
    jAx FT HT false ND NOM a b st = FAIL ∨
      (recOK (FT (cIdx st)) (cIdx st) ND NOM = true ∧ fD (FT (cIdx st)) = 0 ∧
        fJ (FT (cIdx st)) = 0 ∧ fDp (FT (cIdx st)) = 0 ∧
        fPi (FT (cIdx st)) = mul12 (hInv (HT a)) (hMat (HT b)) ∧
        jAx FT HT false ND NOM a b st = mkC (cIdx st + 1) (cNd st)) := by
  simp only [jAx, strictN_eq]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [andB_eq_true, beq_eq_true, mulF_eq] at hb
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h⟩

theorem wEndJ_spec (d p c : ℕ) :
    wEndJ (d, (p, c)) = FAIL ∨
      (dD d = dD0 d ∧ p = dP0 d ∧ c = 509 ∧ wEndJ (d, (p, c)) = mkC (dK d + 1) (dNd d)) := by
  dsimp only [wEndJ]
  refine (brec_cases _ _ _).imp id fun ⟨hb, h⟩ => ?_
  simp only [andB_eq_true, beq_eq_true] at hb
  obtain ⟨h1, h2, h3⟩ := hb
  exact ⟨h1, h2, h3, h⟩

section Group

variable {G : Type*} [Group G]

@[expose] def InK (LET X : ℕ) : Prop := ∃ u : Khat LET, ((u : GLm) : Mat12) = toMat X

open Classical in
@[expose] noncomputable def ev {LET : ℕ} (φ : Khat LET →* G) (X : ℕ) : G :=
  if h : InK LET X then φ h.choose else 1

variable {LET : ℕ}

theorem ev_eq (φ : Khat LET →* G) {X : ℕ} (u : Khat LET) (hu : ((u : GLm) : Mat12) = toMat X) :
    ev φ X = φ u := by
  have h : InK LET X := ⟨u, hu⟩
  unfold ev
  rw [dite_eq_left h]
  congr 1
  exact Subtype.ext (Units.ext (h.choose_spec.trans hu.symm))

theorem InK.mul {A B : ℕ} (hA : InK LET A) (hB : InK LET B) : InK LET (mul12 A B) := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hB
  exact ⟨u * v, by rw [Subgroup.coe_mul, Units.val_mul, hu, hv, toMat_mul12]⟩

theorem ev_mul (φ : Khat LET →* G) {A B : ℕ} (hA : InK LET A) (hB : InK LET B) :
    ev φ (mul12 A B) = ev φ A * ev φ B := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hB
  rw [ev_eq φ (u * v) (by rw [Subgroup.coe_mul, Units.val_mul, hu, hv, toMat_mul12]), ev_eq φ u hu,
    ev_eq φ v hv, map_mul]

theorem InK.cancel_left {A B : ℕ} (hA : InK LET A) (h : InK LET (mul12 A B)) : InK LET B := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨w, hw⟩ := h
  refine ⟨u⁻¹ * w, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hw, toMat_mul12, ← hu, ← mul_assoc,
    Units.inv_mul, one_mul]

theorem InK.cancel_right {A B : ℕ} (hB : InK LET B) (h : InK LET (mul12 A B)) : InK LET A := by
  obtain ⟨v, hv⟩ := hB
  obtain ⟨w, hw⟩ := h
  refine ⟨w * v⁻¹, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hw, toMat_mul12, ← hv, mul_assoc,
    Units.mul_inv, mul_one]

theorem inK_ident : InK LET ident12 :=
  ⟨1, by rw [Subgroup.coe_one, Units.val_one, toMat_ident12]⟩

theorem ev_ident (φ : Khat LET →* G) : ev φ ident12 = 1 := by
  rw [ev_eq φ 1 (by rw [Subgroup.coe_one, Units.val_one, toMat_ident12]), map_one]

theorem InK.of_inv {A B : ℕ} (hA : InK LET A) (h : mul12 A B = ident12) : InK LET B :=
  hA.cancel_left (by rw [h]; exact inK_ident)

theorem InK.of_inv' {A B : ℕ} (hB : InK LET B) (h : mul12 A B = ident12) : InK LET A :=
  hB.cancel_right (by rw [h]; exact inK_ident)

theorem ev_inv (φ : Khat LET →* G) {A B : ℕ} (hA : InK LET A) (h : mul12 A B = ident12) :
    ev φ B = (ev φ A)⁻¹ := by
  have e := ev_mul φ hA (hA.of_inv h)
  rw [h, ev_ident] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem inK_mul_iff_right {A B : ℕ} (hA : InK LET A) : InK LET (mul12 A B) ↔ InK LET B :=
  ⟨hA.cancel_left, hA.mul⟩

theorem inK_mul_iff_left {A B : ℕ} (hB : InK LET B) : InK LET (mul12 A B) ↔ InK LET A :=
  ⟨hB.cancel_right, fun h => h.mul hB⟩

theorem inK_inv_iff {A B : ℕ} (h : mul12 A B = ident12) : InK LET B ↔ InK LET A :=
  ⟨fun hB => hB.of_inv' h, fun hA => hA.of_inv h⟩

theorem toMat_ne_zero_of_mul {A B : ℕ} (h : mul12 A B = ident12) : toMat A ≠ 0 := by
  intro h0
  have e := congrArg toMat h
  rw [toMat_mul12, h0, zero_mul, toMat_ident12] at e
  exact zero_ne_one e

theorem letter_ev (φ : Khat LET →* G) {x y t : G}
    (h01 : chkInv (letMat LET 0) (letMat LET 1) = true)
    (h23 : chkInv (letMat LET 2) (letMat LET 3) = true)
    (hx : ∀ g : Khat LET, (g : GLm) = xh LET → φ g = x)
    (hy : ∀ g : Khat LET, (g : GLm) = yh LET → φ g = y) {c : ℕ} (hc : c < 4) :
    InK LET (letMat LET c) ∧ ev φ (letMat LET c) = lvE (jv x y t 1) c := by
  have gx : xh LET ∈ Khat LET := Subgroup.subset_closure (by simp)
  have gy : yh LET ∈ Khat LET := Subgroup.subset_closure (by simp)
  have ux : (((⟨xh LET, gx⟩ : Khat LET) : GLm) : Mat12) = toMat (letMat LET 0) := val_lu h01
  have uxi : ((((⟨xh LET, gx⟩ : Khat LET)⁻¹ : Khat LET) : GLm) : Mat12) = toMat (letMat LET 1) :=
    val_inv_lu h01
  have uy : (((⟨yh LET, gy⟩ : Khat LET) : GLm) : Mat12) = toMat (letMat LET 2) := val_lu h23
  have uyi : ((((⟨yh LET, gy⟩ : Khat LET)⁻¹ : Khat LET) : GLm) : Mat12) = toMat (letMat LET 3) :=
    val_inv_lu h23
  interval_cases c
  · exact ⟨⟨_, ux⟩, by rw [ev_eq φ _ ux, hx _ rfl]; simp [lvE, jv]⟩
  · exact ⟨⟨_, uxi⟩, by rw [ev_eq φ _ uxi, map_inv, hx _ rfl]; simp [lvE, jv]⟩
  · exact ⟨⟨_, uy⟩, by rw [ev_eq φ _ uy, hy _ rfl]; simp [lvE, jv]⟩
  · exact ⟨⟨_, uyi⟩, by rw [ev_eq φ _ uyi, map_inv, hy _ rfl]; simp [lvE, jv]⟩

theorem lvE_255 (f : ℕ → G) : lvE f 255 = 1 := ite_eq_left rfl

theorem lvE_4 (x y t : G) : lvE (jv x y t 1) 4 = t := by
  simp [lvE, jv]

end Group

section Facts

variable {G : Type*} [Group G] (k : KD) (φ : Khat k.LET →* G) (x y t : G)

@[expose] noncomputable def tJ (J : ℕ) : G :=
  if J = 0 then 1 else (ev φ (oG (k.OT (J - 1))))⁻¹ * t * ev φ (oG (k.OT (J - 1)))

@[expose] def FOK (K : ℕ) : Prop :=
  ∀ g < K, recOK (k.FT g) g k.ND k.NOM = true ∧ InK k.LET (fPi (k.FT g))

@[expose] def FRel (w : ℕ → G) (g : ℕ) : Prop :=
  RelT φ.range (w (fD (k.FT g)) * tJ k φ t (fJ (k.FT g))) (w (fDp (k.FT g)) * ev φ (fPi (k.FT g)))

@[expose] def Good (K nd : ℕ) : Prop :=
  0 < nd ∧ FOK k K ∧ ∃ w₀ : ℕ → G, w₀ 0 = 1 ∧
    ∀ w : ℕ → G, (∀ D < nd, w D = w₀ D) → ∀ g < K, FRel k φ t w g

@[expose] def CInv (c : ℕ) : Prop := 2 ^ 20 ≤ cIdx c ∨ Good k φ t (cIdx c) (cNd c)

@[expose] def WG (d p c : ℕ) : Prop :=
  ∃ W n i : ℕ, W < 256 ^ n ∧ i ≤ n ∧ Cur c W n i ∧ wordVal (lvE (jv x y t 1)) W n = 1 ∧
    dK d < 2 ^ 20 ∧ 0 < dNd d ∧ recOK (k.FT (dK d)) (dK d) k.ND k.NOM = true ∧ InK k.LET (dP0 d) ∧
    FOK k (dK d) ∧ (c % 2 = 0 → InK k.LET p) ∧
    (c % 2 = 1 → (InK k.LET p ↔ InK k.LET (fPi (k.FT (dK d))))) ∧
    ∃ w₀ : ℕ → G, w₀ 0 = 1 ∧ ∀ w : ℕ → G, (∀ D < dNd d, w D = w₀ D) →
      (∀ g < dK d, FRel k φ t w g) ∧
      (c % 2 = 0 → RelT φ.range (w (dD0 d) * ev φ (dP0 d) * wordVal (lvE (jv x y t 1)) W i)
        (w (dD d) * ev φ p)) ∧
      (c % 2 = 1 → InK k.LET (fPi (k.FT (dK d))) → ∃ A B Q : G,
        RelT φ.range (w (dD0 d) * ev φ (dP0 d) * Q) A ∧
        RelT φ.range (B * Q⁻¹ * wordVal (lvE (jv x y t 1)) W i) (w (dD d) * ev φ p) ∧
        (RelT φ.range A B → FRel k φ t w (dK d)))

@[expose] def QInv (q : ℕ × St) : Prop :=
  (q.1 % 2 = 0 ∧ CInv k φ t (q.1 / 2)) ∨
    (q.1 % 2 = 1 ∧ (q.2.2.2 = 0 ∨ WG k φ x y t q.2.1 q.2.2.1 q.2.2.2))

structure Hyp : Prop where
  h01 : chkInv (letMat k.LET 0) (letMat k.LET 1) = true
  h23 : chkInv (letMat k.LET 2) (letMat k.LET 3) = true
  hx : ∀ g : Khat k.LET, (g : GLm) = xh k.LET → φ g = x
  hy : ∀ g : Khat k.LET, (g : GLm) = yh k.LET → φ g = y
  ht : t * t = 1
  hdr : ∀ a < 2 ^ 16, 0 < k.HT a →
    InK k.LET (hMat (k.HT a)) ∧ mul12 (hMat (k.HT a)) (hInv (k.HT a)) = ident12
  om : ∀ j < k.NOM, k.OT j ≠ 0 →
    InK k.LET (oG (k.OT j)) ∧ mul12 (oG (k.OT j)) (oGi' (k.OT j)) = ident12
  psi : ∀ e < 512, ∀ h τ : ℕ, τ < 2 ^ 144 → inT k.TH (lamT (k.LT e)) h τ = true →
    (InK k.LET τ ↔ InK k.LET (mul12 (lP' (k.LT e)) (Nat.land τ linMask))) ∧
    (InK k.LET τ → t * ev φ τ * t = ev φ (mul12 (lP' (k.LT e)) (Nat.land τ linMask)))
  words : ∀ w < 2 ^ 16, wW (k.WT w) < 256 ^ wN (k.WT w) ∧
    wordVal (lvE (jv x y t 1)) (wW (k.WT w)) (wN (k.WT w)) = 1

variable {k φ x y t}

theorem tJ_zero : tJ k φ t 0 = 1 := ite_eq_left rfl

theorem cinv_FAIL : CInv k φ t FAIL := Or.inl (by rw [cIdx_FAIL]; norm_num)

theorem good_of_cinv {c : ℕ} (h : CInv k φ t c) (hr : recOK (k.FT (cIdx c)) (cIdx c) k.ND k.NOM = true) :
    Good k φ t (cIdx c) (cNd c) :=
  h.resolve_left (by have e := (recOK_spec hr).1; have := fIdx_lt (k.FT (cIdx c)); omega)

theorem cinv_init : CInv k φ t (mkC 0 1) := by
  refine Or.inr ?_
  rw [cIdx_mkC (by norm_num), cNd_mkC (by norm_num) (by norm_num)]
  exact ⟨by norm_num, fun g hg => absurd hg (Nat.not_lt_zero _), fun _ => 1, rfl,
    fun _ _ g hg => absurd hg (Nat.not_lt_zero _)⟩

theorem wg_rec {d p c : ℕ} (hs : WG k φ x y t d p c) : recOK (k.FT (dK d)) (dK d) k.ND k.NOM = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := hs
  exact h

theorem wg_fok {d p c : ℕ} (hs : WG k φ x y t d p c) : FOK k (dK d) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hs
  exact h

theorem jTree_good {c : ℕ} (h : CInv k φ t c) : CInv k φ t (jTree k.FT false k.ND k.NOM c) := by
  rcases jTree_spec k.FT k.ND k.NOM c with e | ⟨hr, -, hDp, hD, hπ, e⟩
  · rw [e]
    exact cinv_FAIL
  rw [e]
  obtain ⟨-, hfok, w₀, hw0, hw⟩ := good_of_cinv h hr
  have hK20 : cIdx c < 2 ^ 20 := (recOK_spec hr).1 ▸ fIdx_lt _
  have hn16 : cNd c < 2 ^ 16 := hDp ▸ fDp_lt _
  refine Or.inr ?_
  rw [cIdx_mkC (by omega), cNd_mkC (by omega) (by omega)]
  refine ⟨by omega, fun g hg => ?_, Function.update w₀ (cNd c)
    (w₀ (fD (k.FT (cIdx c))) * tJ k φ t (fJ (k.FT (cIdx c)))), ?_, fun w hag g hg => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact hfok g hg
    · exact ⟨hr, by rw [hπ]; exact inK_ident⟩
  · rw [Function.update_of_ne (by omega)]
    exact hw0
  · have hag' : ∀ D < cNd c, w D = w₀ D := fun D hD' => by
      rw [hag D (by omega), Function.update_of_ne (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact hw w hag' g hg
    · unfold FRel
      apply RelT.of_eq
      rw [hπ, ev_ident, mul_one, hDp, hag (cNd c) (by omega), Function.update_self, hag' _ hD]

theorem jAx_good (H : Hyp k φ x y t) {c : ℕ} (a b : ℕ) (ha16 : a < 2 ^ 16) (hb16 : b < 2 ^ 16)
    (h : CInv k φ t c) :
    CInv k φ t (jAx k.FT k.HT false k.ND k.NOM a b c) := by
  rcases jAx_spec k.FT k.HT k.ND k.NOM a b c with e | ⟨hr, hD, hJ, hDp, hπ, e⟩
  · rw [e]
    exact cinv_FAIL
  rw [e]
  obtain ⟨hnd, hfok, w₀, hw0, hw⟩ := good_of_cinv h hr
  have hK20 : cIdx c < 2 ^ 20 := (recOK_spec hr).1 ▸ fIdx_lt _
  have hπK : InK k.LET (fPi (k.FT (cIdx c))) := by
    have hne := toMat_ne_zero_of_mul (recOK_spec hr).2.2.2.2
    rw [hπ, toMat_mul12] at hne
    have ha : 0 < k.HT a := by
      refine Nat.pos_of_ne_zero fun h0 => hne ?_
      rw [h0, show hInv 0 = 0 from rfl, toMat_zero, zero_mul]
    have hb : 0 < k.HT b := by
      refine Nat.pos_of_ne_zero fun h0 => hne ?_
      rw [h0, show hMat 0 = 0 from rfl, toMat_zero, mul_zero]
    obtain ⟨hA, hAi⟩ := H.hdr a ha16 ha
    rw [hπ]
    exact (hA.of_inv hAi).mul (H.hdr b hb16 hb).1
  refine Or.inr ?_
  rw [cIdx_mkC (by omega), cNd_mkC (by omega) (cNd_lt c)]
  refine ⟨hnd, fun g hg => ?_, w₀, hw0, fun w hag g hg => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact hfok g hg
    · exact ⟨hr, hπK⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact hw w hag g hg
    · obtain ⟨u, hu⟩ := hπK
      unfold FRel RelT
      rw [hD, hDp, hJ, ev_eq φ u hu, tJ_zero, (hag 0 hnd).trans hw0]
      have e2 : (1 : G) * 1 * (1 * φ u)⁻¹ = (φ u)⁻¹ := by group
      rw [e2]
      exact φ.range.inv_mem ⟨u, rfl⟩

theorem stS_good (H : Hyp k φ x y t) {c : ℕ} (a b D0 w : ℕ) (ha16 : a < 2 ^ 16) (hb16 : b < 2 ^ 16)
    (hD0 : D0 < 2 ^ 16) (hw16 : w < 2 ^ 16) (h : CInv k φ t c) :
    (stS k.FT k.HT k.WT k.ND k.NOM a b D0 w c).2.2 = 0 ∨
      WG k φ x y t (stS k.FT k.HT k.WT k.ND k.NOM a b D0 w c).1
        (stS k.FT k.HT k.WT k.ND k.NOM a b D0 w c).2.1
        (stS k.FT k.HT k.WT k.ND k.NOM a b D0 w c).2.2 := by
  rcases stS_spec k.FT k.HT k.WT k.ND k.NOM a b D0 w c with e | ⟨ha, hb, -, hr, e⟩
  · rw [e]
    exact Or.inl rfl
  rw [e]
  refine Or.inr ?_
  obtain ⟨hnd, hfok, w₀, hw0, hw⟩ := good_of_cinv h hr
  have hK20 : cIdx c < 2 ^ 20 := (recOK_spec hr).1 ▸ fIdx_lt _
  obtain ⟨hA, hAi⟩ := H.hdr a ha16 ha
  have hP0 : InK k.LET (mul12 (hInv (k.HT a)) (hMat (k.HT b))) :=
    (hA.of_inv hAi).mul (H.hdr b hb16 hb).1
  obtain ⟨hWlt, hWv⟩ := H.words w hw16
  have hK32 := cIdx_lt c
  have hn32 := cNd_lt c
  unfold WG
  dsimp only
  rw [dK_mkD _ hD0 hK32 hn32, dNd_mkD _ hD0 hK32 hn32, dD0_mkD _ hD0 hK32 hn32,
    dD_mkD _ hD0 hK32 hn32, dP0_mkD _ hD0 hK32 hn32, wInit_mod hWlt]
  refine ⟨_, _, 0, hWlt, Nat.zero_le _, cur_init hWlt, hWv, hK20, hnd, hr, hP0, hfok, fun _ => hP0,
    fun h1 => absurd h1 (by norm_num), w₀, hw0, fun w' hag => ⟨hw w' hag, fun _ => ?_,
    fun h1 => absurd h1 (by norm_num)⟩⟩
  rw [wordVal_zero, mul_one]
  exact RelT.refl _

theorem wEndJ_good {d p c : ℕ} (hs : c = 0 ∨ WG k φ x y t d p c) :
    CInv k φ t (wEndJ (d, (p, c))) := by
  rcases wEndJ_spec d p c with e | ⟨hD, hp, hc, e⟩
  · rw [e]
    exact cinv_FAIL
  rw [e]
  rcases hs with h0 | hs
  · omega
  obtain ⟨W, n, i, -, hin, hcur, hv, hK, hnd, hrec, hP0, hfok, -, hf1, w₀, hw0, hw⟩ := hs
  subst hc
  have hin' := cur_end hin hcur
  have hπ : InK k.LET (fPi (k.FT (dK d))) := (hf1 (by norm_num)).1 (hp ▸ hP0)
  refine Or.inr ?_
  rw [cIdx_mkC (by omega), cNd_mkC (by omega) (dNd_lt d)]
  refine ⟨hnd, fun g hg => ?_, w₀, hw0, fun w hag g hg => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact hfok g hg
    · exact ⟨hrec, hπ⟩
  · obtain ⟨hg', -, h1⟩ := hw w hag
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact hg' g hg
    · obtain ⟨A, B, Q, hA, hB, hAB⟩ := h1 (by norm_num) hπ
      apply hAB
      rw [hin', hv, mul_one, hD] at hB
      have h2 := hB.mul_right Q
      rw [inv_mul_cancel_right] at h2
      rw [← hp] at hA
      exact hA.symm.trans h2.symm

theorem wg_ord {d p c d' p' : ℕ} (hs : WG k φ x y t d p c) (hl : letAt c ≠ 254)
    (hK' : dK d' = dK d) (hN' : dNd d' = dNd d) (hD0' : dD0 d' = dD0 d) (hP0' : dP0 d' = dP0 d)
    (hiff : FOK k (dK d) → (InK k.LET p ↔ InK k.LET p'))
    (hrel : ∀ w : ℕ → G, FOK k (dK d) → (∀ g < dK d, FRel k φ t w g) → InK k.LET p →
      RelT φ.range (w (dD d) * ev φ p * lvE (jv x y t 1) (letAt c)) (w (dD d') * ev φ p')) :
    WG k φ x y t d' p' (adv c 1 0) := by
  obtain ⟨W, n, i, hW, hin, hc, hv, hK, hnd, hrec, hP0, hfok, hf0, hf1, w₀, hw0, hw⟩ := hs
  obtain ⟨hi, hlet⟩ := cur_letter hW hin hc hl
  refine ⟨W, n, i + 1, hW, hi, cur_adv (by norm_num) hc, hv, ?_⟩
  rw [hK', hN', hD0', hP0', adv_mod0]
  refine ⟨hK, hnd, hrec, hP0, hfok, fun h0 => (hiff hfok).1 (hf0 h0),
    fun h1 => (hiff hfok).symm.trans (hf1 h1), w₀, hw0, fun w hag => ?_⟩
  obtain ⟨hg, hr0, hr1⟩ := hw w hag
  refine ⟨hg, fun h0 => ?_, fun h1 hπ => ?_⟩
  · rw [wordVal_succ, ← hlet, ← mul_assoc]
    exact ((hr0 h0).mul_right _).trans (hrel w hfok hg (hf0 h0))
  · obtain ⟨A, B, Q, hA, hB, hAB⟩ := hr1 h1 hπ
    refine ⟨A, B, Q, hA, ?_, hAB⟩
    rw [wordVal_succ, ← hlet, ← mul_assoc]
    exact (hB.mul_right _).trans (hrel w hfok hg ((hf1 h1).2 hπ))

theorem wg_own {d p c d' p' : ℕ} (hs : WG k φ x y t d p c) (hflag : c % 2 = 0)
    (hl : letAt c ≠ 254)
    (hK' : dK d' = dK d) (hN' : dNd d' = dNd d) (hD0' : dD0 d' = dD0 d) (hP0' : dP0 d' = dP0 d)
    (hiff : InK k.LET p → (InK k.LET p' ↔ InK k.LET (fPi (k.FT (dK d)))))
    (hrel : ∀ w : ℕ → G, InK k.LET p → InK k.LET (fPi (k.FT (dK d))) →
      RelT φ.range (w (dD d) * ev φ p * lvE (jv x y t 1) (letAt c)) (w (dD d') * ev φ p') →
      FRel k φ t w (dK d)) :
    WG k φ x y t d' p' (adv c 1 1) := by
  obtain ⟨W, n, i, hW, hin, hc, hv, hK, hnd, hrec, hP0, hfok, hf0, -, w₀, hw0, hw⟩ := hs
  obtain ⟨hi, hlet⟩ := cur_letter hW hin hc hl
  have hp := hf0 hflag
  refine ⟨W, n, i + 1, hW, hi, cur_adv (by norm_num) hc, hv, ?_⟩
  rw [hK', hN', hD0', hP0', adv_mod1]
  refine ⟨hK, hnd, hrec, hP0, hfok, fun h => absurd h (by norm_num), fun _ => hiff hp, w₀, hw0,
    fun w hag => ?_⟩
  obtain ⟨hg, hr0, -⟩ := hw w hag
  refine ⟨hg, fun h => absurd h (by norm_num), fun _ hπ =>
    ⟨_, _, wordVal (lvE (jv x y t 1)) W (i + 1), ?_, ?_, hrel w hp hπ⟩⟩
  · rw [wordVal_succ, ← hlet, ← mul_assoc]
    exact (hr0 hflag).mul_right _
  · exact RelT.of_eq (by group)

theorem sNs_good (H : Hyp k φ x y t) {d p c : ℕ} (hs : c = 0 ∨ WG k φ x y t d p c) :
    (sNs k.LET (d, (p, c))).2.2 = 0 ∨ WG k φ x y t (sNs k.LET (d, (p, c))).1
      (sNs k.LET (d, (p, c))).2.1 (sNs k.LET (d, (p, c))).2.2 := by
  rcases sNs_spec k.LET d p c with e | ⟨hl, e⟩
  · rw [e]
    exact Or.inl rfl
  rw [e]
  rcases hs with h0 | hs
  · subst h0
    exact Or.inl (by simp [adv0_eq])
  refine Or.inr ?_
  dsimp only
  obtain ⟨hL, hev⟩ := letter_ev φ (t := t) H.h01 H.h23 H.hx H.hy hl
  refine wg_ord hs (by omega) rfl rfl rfl rfl (fun _ => (inK_mul_iff_left hL).symm)
    fun w _ _ hp => ?_
  rw [ev_mul φ hp hL, hev, mul_assoc]
  exact RelT.refl _

theorem sEfs_good {S g d p c : ℕ} (hs : c = 0 ∨ WG k φ x y t d p c) (hS : S < 2) :
    (sEfs k.FT S g (d, (p, c))).2.2 = 0 ∨ WG k φ x y t (sEfs k.FT S g (d, (p, c))).1
      (sEfs k.FT S g (d, (p, c))).2.1 (sEfs k.FT S g (d, (p, c))).2.2 := by
  rcases sEfs_spec k.FT S g d p c with e | ⟨hl, hr, hD, hJ, e⟩
  · rw [e]
    exact Or.inl rfl
  rw [e]
  rcases hs with h0 | hs
  · subst h0
    exact absurd hl (by decide)
  refine Or.inr ?_
  dsimp only
  have hDp := fDp_lt (k.FT g)
  have hl' : letAt c ≠ 254 := by rw [hl]; decide
  have key : ∀ w : ℕ → G, InK k.LET p → InK k.LET (fPi (k.FT g)) →
      (RelT φ.range (w (dD d) * ev φ p * lvE (jv x y t 1) (letAt c))
        (w (dD (setD d (fDp (k.FT g)))) * ev φ (mul12 (fPi (k.FT g)) p)) ↔ FRel k φ t w g) := by
    intro w hp hπ
    unfold FRel
    rw [dD_setD d hDp, ev_mul φ hπ hp, hl, lvE_255, hD, hJ, tJ_zero]
    exact CFSG.Certificates.DceTw.eps_fwd (N := φ.range) (a := w (fD (k.FT g)))
      (b := w (fDp (k.FT g))) (r := ev φ (fPi (k.FT g))) (p := ev φ p)
  rcases refS_spec hr with ⟨rfl, rfl, hc⟩ | ⟨hS1, hg⟩
  · exact wg_own hs hc hl' (dK_setD d hDp) (dNd_setD d hDp) (dD0_setD d hDp) (dP0_setD d hDp)
      (fun hp => inK_mul_iff_left hp) fun w hp hπ hR => (key w hp hπ).1 hR
  · obtain rfl : S = 0 := by omega
    have hπ := (wg_fok hs g hg).2
    exact wg_ord hs hl' (dK_setD d hDp) (dNd_setD d hDp) (dD0_setD d hDp) (dP0_setD d hDp)
      (fun _ => (inK_mul_iff_right hπ).symm) fun w _ hR hp => (key w hp hπ).2 (hR g hg)

theorem sEbs_good {S g d p c : ℕ} (hs : c = 0 ∨ WG k φ x y t d p c) (hS : S < 2) :
    (sEbs k.FT S g (d, (p, c))).2.2 = 0 ∨ WG k φ x y t (sEbs k.FT S g (d, (p, c))).1
      (sEbs k.FT S g (d, (p, c))).2.1 (sEbs k.FT S g (d, (p, c))).2.2 := by
  rcases sEbs_spec k.FT S g d p c with e | ⟨hl, hr, hD, hJ, e⟩
  · rw [e]
    exact Or.inl rfl
  rw [e]
  rcases hs with h0 | hs
  · subst h0
    exact absurd hl (by decide)
  refine Or.inr ?_
  dsimp only
  have hDf := fD_lt (k.FT g)
  have hl' : letAt c ≠ 254 := by rw [hl]; decide
  have hm : mul12 (fPi (k.FT g)) (fPiI (k.FT g)) = ident12 := by
    rcases refS_spec hr with ⟨-, rfl, -⟩ | ⟨-, hg⟩
    · exact (recOK_spec (wg_rec hs)).2.2.2.2
    · exact (recOK_spec (wg_fok hs g hg).1).2.2.2.2
  have key : ∀ w : ℕ → G, InK k.LET p → InK k.LET (fPi (k.FT g)) →
      (RelT φ.range (w (dD d) * ev φ p * lvE (jv x y t 1) (letAt c))
        (w (dD (setD d (fD (k.FT g)))) * ev φ (mul12 (fPiI (k.FT g)) p)) ↔ FRel k φ t w g) := by
    intro w hp hπ
    unfold FRel
    rw [dD_setD d hDf, ev_mul φ (hπ.of_inv hm) hp, ev_inv φ hπ hm, hl, lvE_255, hD, hJ, tJ_zero]
    exact CFSG.Certificates.DceTw.eps_bwd (N := φ.range) (a := w (fD (k.FT g)))
      (b := w (fDp (k.FT g))) (r := ev φ (fPi (k.FT g))) (p := ev φ p)
  rcases refS_spec hr with ⟨rfl, rfl, hc⟩ | ⟨hS1, hg⟩
  · exact wg_own hs hc hl' (dK_setD d hDf) (dNd_setD d hDf) (dD0_setD d hDf) (dP0_setD d hDf)
      (fun hp => (inK_mul_iff_left hp).trans (inK_inv_iff hm)) fun w hp hπ hR => (key w hp hπ).1 hR
  · obtain rfl : S = 0 := by omega
    have hπ := (wg_fok hs g hg).2
    exact wg_ord hs hl' (dK_setD d hDf) (dNd_setD d hDf) (dD0_setD d hDf) (dP0_setD d hDf)
      (fun _ => (inK_mul_iff_right (hπ.of_inv hm)).symm) fun w _ hR hp => (key w hp hπ).2 (hR g hg)

theorem slot (H : Hyp k φ x y t) {J : ℕ} (hJ0 : 0 < J) (hJN : J ≤ k.NOM)
    (hO : oJ (k.OT (J - 1)) = J) :
    InK k.LET (oG (k.OT (J - 1))) ∧ mul12 (oG (k.OT (J - 1))) (oGi' (k.OT (J - 1))) = ident12 ∧
      tJ k φ t J = (ev φ (oG (k.OT (J - 1))))⁻¹ * t * ev φ (oG (k.OT (J - 1))) := by
  have hne : k.OT (J - 1) ≠ 0 := fun h0 => by
    rw [h0, show oJ 0 = 0 from rfl] at hO
    omega
  obtain ⟨h1, h2⟩ := H.om (J - 1) (by omega) hne
  exact ⟨h1, h2, ite_eq_right (by omega)⟩

theorem sUfs_good (H : Hyp k φ x y t) {S g e h TAU d p c : ℕ} (hs : c = 0 ∨ WG k φ x y t d p c)
    (hS : S < 2) :
    (sUfs k.FT k.OT k.LT k.TH S g e h TAU (d, (p, c))).2.2 = 0 ∨
      WG k φ x y t (sUfs k.FT k.OT k.LT k.TH S g e h TAU (d, (p, c))).1
        (sUfs k.FT k.OT k.LT k.TH S g e h TAU (d, (p, c))).2.1
        (sUfs k.FT k.OT k.LT k.TH S g e h TAU (d, (p, c))).2.2 := by
  rcases sUfs_spec k.FT k.OT k.LT k.TH S g e h TAU d p c with E | ⟨hl, hr, hD, hJ0, hO, he, hτ, hin, E⟩
  · rw [E]
    exact Or.inl rfl
  rw [E]
  rcases hs with h0 | hs
  · subst h0
    exact absurd hl (by decide)
  refine Or.inr ?_
  dsimp only
  subst hτ
  have hDp := fDp_lt (k.FT g)
  have hl' : letAt c ≠ 254 := by rw [hl]; decide
  have hJN : fJ (k.FT g) ≤ k.NOM := by
    rcases refS_spec hr with ⟨-, rfl, -⟩ | ⟨-, hg⟩
    · exact (recOK_spec (wg_rec hs)).2.2.2.1
    · exact (recOK_spec (wg_fok hs g hg).1).2.2.2.1
  obtain ⟨hg1, hgg, htJ⟩ := slot H hJ0 hJN hO
  generalize k.OT (fJ (k.FT g) - 1) = O at hg1 hgg htJ hin ⊢
  have hGi := hg1.of_inv hgg
  have evGi := ev_inv φ hg1 hgg
  obtain ⟨hψi, hψr⟩ := H.psi e he h _ (mul12_lt _ _) hin
  have tinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right H.ht
  have A1 : InK k.LET p ↔ InK k.LET (mul12 (lP' (k.LT e)) (Nat.land (mul12 (oG O) p) linMask)) :=
    (inK_mul_iff_right hg1).symm.trans hψi
  have key : ∀ w : ℕ → G, InK k.LET p → InK k.LET (fPi (k.FT g)) →
      (RelT φ.range (w (dD d) * ev φ p * lvE (jv x y t 1) (letAt c))
        (w (dD (setD d (fDp (k.FT g)))) * ev φ (mul12 (mul12 (fPi (k.FT g)) (oGi' O))
          (mul12 (lP' (k.LT e)) (Nat.land (mul12 (oG O) p) linMask)))) ↔ FRel k φ t w g) := by
    intro w hp hπ
    have hT : InK k.LET (mul12 (oG O) p) := hg1.mul hp
    unfold FRel
    rw [dD_setD d hDp, hl, lvE_4, hD, ev_mul φ (hπ.mul hGi) (hψi.1 hT), ev_mul φ hπ hGi, evGi, htJ]
    exact CFSG.Certificates.DceTw.u_fwd (N := φ.range) (a := w (fD (k.FT g)))
      (b := w (fDp (k.FT g))) (r := ev φ (fPi (k.FT g))) (p := ev φ p) (g := ev φ (oG O))
      (σ := ev φ (mul12 (oG O) p))
      (τ := ev φ (mul12 (lP' (k.LT e)) (Nat.land (mul12 (oG O) p) linMask))) (u := t)
      (ev_mul φ hg1 hp) (by rw [tinv]; exact hψr hT)
  rcases refS_spec hr with ⟨rfl, rfl, hc⟩ | ⟨hS1, hg⟩
  · exact wg_own hs hc hl' (dK_setD d hDp) (dNd_setD d hDp) (dD0_setD d hDp) (dP0_setD d hDp)
      (fun hp => (inK_mul_iff_left (A1.1 hp)).trans (inK_mul_iff_left hGi))
      fun w hp hπ hR => (key w hp hπ).1 hR
  · obtain rfl : S = 0 := by omega
    have hπ := (wg_fok hs g hg).2
    exact wg_ord hs hl' (dK_setD d hDp) (dNd_setD d hDp) (dD0_setD d hDp) (dP0_setD d hDp)
      (fun _ => A1.trans (inK_mul_iff_right (hπ.mul hGi)).symm)
      fun w _ hR hp => (key w hp hπ).2 (hR g hg)

theorem sUbs_good (H : Hyp k φ x y t) {S g e h RHO d p c : ℕ} (hs : c = 0 ∨ WG k φ x y t d p c)
    (hS : S < 2) :
    (sUbs k.FT k.OT k.LT k.TH S g e h RHO (d, (p, c))).2.2 = 0 ∨
      WG k φ x y t (sUbs k.FT k.OT k.LT k.TH S g e h RHO (d, (p, c))).1
        (sUbs k.FT k.OT k.LT k.TH S g e h RHO (d, (p, c))).2.1
        (sUbs k.FT k.OT k.LT k.TH S g e h RHO (d, (p, c))).2.2 := by
  rcases sUbs_spec k.FT k.OT k.LT k.TH S g e h RHO d p c with E | ⟨hl, hr, hD, hJ0, hO, he, hρ, hin, E⟩
  · rw [E]
    exact Or.inl rfl
  rw [E]
  rcases hs with h0 | hs
  · subst h0
    exact absurd hl (by decide)
  refine Or.inr ?_
  dsimp only
  subst hρ
  have hDf := fD_lt (k.FT g)
  have hl' : letAt c ≠ 254 := by rw [hl]; decide
  have hJm : fJ (k.FT g) ≤ k.NOM ∧ mul12 (fPi (k.FT g)) (fPiI (k.FT g)) = ident12 := by
    rcases refS_spec hr with ⟨-, rfl, -⟩ | ⟨-, hg⟩
    · exact ⟨(recOK_spec (wg_rec hs)).2.2.2.1, (recOK_spec (wg_rec hs)).2.2.2.2⟩
    · exact ⟨(recOK_spec (wg_fok hs g hg).1).2.2.2.1, (recOK_spec (wg_fok hs g hg).1).2.2.2.2⟩
  obtain ⟨hJN, hm⟩ := hJm
  obtain ⟨hg1, hgg, htJ⟩ := slot H hJ0 hJN hO
  generalize k.OT (fJ (k.FT g) - 1) = O at hg1 hgg htJ hin ⊢
  have hGi := hg1.of_inv hgg
  have evGi := ev_inv φ hg1 hgg
  obtain ⟨hψi, hψr⟩ := H.psi e he h _ (mul12_lt _ _) hin
  have tinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right H.ht
  have B2 := inK_mul_iff_right (B := mul12 (lP' (k.LT e))
    (Nat.land (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) linMask)) hGi
  have B1 : InK k.LET (fPi (k.FT g)) → (InK k.LET p ↔ InK k.LET (mul12 (lP' (k.LT e))
      (Nat.land (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) linMask))) := fun hπ =>
    (inK_mul_iff_right (hg1.mul (hπ.of_inv hm))).symm.trans hψi
  have B3 : InK k.LET p → (InK k.LET (mul12 (lP' (k.LT e))
      (Nat.land (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) linMask)) ↔ InK k.LET (fPi (k.FT g))) :=
    fun hp => hψi.symm.trans ((inK_mul_iff_left hp).trans ((inK_mul_iff_right hg1).trans
      (inK_inv_iff hm)))
  have key : ∀ w : ℕ → G, InK k.LET p → InK k.LET (fPi (k.FT g)) →
      (RelT φ.range (w (dD d) * ev φ p * lvE (jv x y t 1) (letAt c))
        (w (dD (setD d (fD (k.FT g)))) * ev φ (mul12 (oGi' O) (mul12 (lP' (k.LT e))
          (Nat.land (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) linMask)))) ↔ FRel k φ t w g) := by
    intro w hp hπ
    have hπi := hπ.of_inv hm
    have hρK : InK k.LET (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) := (hg1.mul hπi).mul hp
    unfold FRel
    rw [dD_setD d hDf, hl, lvE_4, hD, ev_mul φ hGi (hψi.1 hρK), evGi, htJ]
    have hσ : ev φ (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) =
        ev φ (oG O) * (ev φ (fPi (k.FT g)))⁻¹ * ev φ p := by
      rw [ev_mul φ (hg1.mul hπi) hp, ev_mul φ hg1 hπi, ev_inv φ hπ hm]
    have hτ' : t⁻¹ * ev φ (mul12 (lP' (k.LT e))
        (Nat.land (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) linMask)) * t =
        ev φ (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) := by
      rw [← hψr hρK, tinv]
      calc t * (t * ev φ (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) * t) * t
          = (t * t) * ev φ (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) * (t * t) := by group
        _ = _ := by rw [H.ht, one_mul, mul_one]
    have := CFSG.Certificates.DceTw.U_bwd (N := φ.range) (a := w (fD (k.FT g)))
      (b := w (fDp (k.FT g))) (r := ev φ (fPi (k.FT g))) (p := ev φ p) (g := ev φ (oG O))
      (σ := ev φ (mul12 (lP' (k.LT e))
        (Nat.land (mul12 (mul12 (oG O) (fPiI (k.FT g))) p) linMask)))
      (τ := ev φ (mul12 (mul12 (oG O) (fPiI (k.FT g))) p)) (u := t) hσ hτ'
    rwa [tinv] at this
  rcases refS_spec hr with ⟨rfl, rfl, hc⟩ | ⟨hS1, hg⟩
  · exact wg_own hs hc hl' (dK_setD d hDf) (dNd_setD d hDf) (dD0_setD d hDf) (dP0_setD d hDf)
      (fun hp => B2.trans (B3 hp)) fun w hp hπ hR => (key w hp hπ).1 hR
  · obtain rfl : S = 0 := by omega
    have hπ := (wg_fok hs g hg).2
    exact wg_ord hs hl' (dK_setD d hDf) (dNd_setD d hDf) (dD0_setD d hDf) (dP0_setD d hDf)
      (fun _ => (B1 hπ).trans B2.symm) fun w _ hR hp => (key w hp hπ).2 (hR g hg)

theorem bsel_t {α : Type} (a b : α) : bsel true a b = a := rfl
theorem bsel_f {α : Type} (a b : α) : bsel false a b = b := rfl

omit [Group G] in
theorem kStep_eq (k : KD) (cd pl m : ℕ) (s : St) : kStep k cd pl (m, s) =
    bsel (Nat.beq (Nat.land m 1) 0)
      (bsel (Nat.beq cd 5)
        (1, stS k.FT k.HT k.WT k.ND k.NOM (f16 pl 0) (f16 pl 16) (f16 pl 32) (f16 pl 48)
          (Nat.shiftRight m 1))
      (bsel (Nat.beq cd 7) (2 * jTree k.FT false k.ND k.NOM (Nat.shiftRight m 1), bad)
      (bsel (Nat.beq cd 8)
        (2 * jAx k.FT k.HT false k.ND k.NOM (f16 pl 0) (f16 pl 16) (Nat.shiftRight m 1), bad)
        kFail)))
      (bsel (Nat.beq cd 0) (1, sNs k.LET s)
      (bsel (Nat.beq cd 1) (1, sEfs k.FT (Nat.land pl 1) (f16 pl 1) s)
      (bsel (Nat.beq cd 2) (1, sEbs k.FT (Nat.land pl 1) (f16 pl 1) s)
      (bsel (Nat.beq cd 3) (1, sUfs k.FT k.OT k.LT k.TH (Nat.land pl 1) (f16 pl 1) (f16 pl 17)
          (Nat.land (Nat.shiftRight pl 33) 7) (Nat.land (Nat.shiftRight pl 36) mask144) s)
      (bsel (Nat.beq cd 4) (1, sUbs k.FT k.OT k.LT k.TH (Nat.land pl 1) (f16 pl 1) (f16 pl 17)
          (Nat.land (Nat.shiftRight pl 33) 7) (Nat.land (Nat.shiftRight pl 36) mask144) s)
      (bsel (Nat.beq cd 6) (2 * wEndJ s, bad) kFail)))))) := rfl

omit [Group G] in
theorem endK_eq (m : ℕ) (s : St) : endK (m, s) = bsel (Nat.beq (Nat.land m 1) 0) (Nat.shiftRight m 1) FAIL :=
  rfl

theorem q2_good {X : ℕ} (h : CInv k φ t X) : QInv k φ x y t (2 * X, bad) :=
  Or.inl ⟨show 2 * X % 2 = 0 by omega, show CInv k φ t (2 * X / 2) by
    rwa [Nat.mul_div_cancel_left X (by norm_num : 0 < 2)]⟩

theorem q1_good {s : St} (h : s.2.2 = 0 ∨ WG k φ x y t s.1 s.2.1 s.2.2) : QInv k φ x y t (1, s) :=
  Or.inr ⟨by norm_num, h⟩

omit [Group G] in
theorem land1 (m : ℕ) : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m

omit [Group G] in
theorem shr1 (m : ℕ) : Nat.shiftRight m 1 = m / 2 := by
  change m >>> 1 = m / 2
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem kStep_good (H : Hyp k φ x y t) (cd pl : ℕ) {q : ℕ × St} (hq : QInv k φ x y t q) :
    QInv k φ x y t (kStep k cd pl q) := by
  obtain ⟨m, d, p, c⟩ := q
  have hS : Nat.land pl 1 < 2 := by
    rw [land1]
    exact Nat.mod_lt _ (by norm_num)
  rw [kStep_eq, land1, shr1]
  unfold QInv at hq
  dsimp only at hq
  rcases hq with ⟨hm, hx⟩ | ⟨hm, hs⟩
  · rw [show Nat.beq (m % 2) 0 = true from beq_eq_true.2 hm, bsel_t]
    cases h5 : Nat.beq cd 5
    · rw [bsel_f]
      cases h7 : Nat.beq cd 7
      · rw [bsel_f]
        cases h8 : Nat.beq cd 8
        · rw [bsel_f]
          exact q2_good cinv_FAIL
        · rw [bsel_t]
          exact q2_good (jAx_good H _ _ (f16_lt _ _) (f16_lt _ _) hx)
      · rw [bsel_t]
        exact q2_good (jTree_good hx)
    · rw [bsel_t]
      exact q1_good (stS_good H _ _ _ _ (f16_lt _ _) (f16_lt _ _) (f16_lt _ _) (f16_lt _ _) hx)
  · have hb : Nat.beq (m % 2) 0 = false := by
      cases e : Nat.beq (m % 2) 0
      · rfl
      · rw [beq_eq_true.1 e] at hm
        exact absurd hm (by norm_num)
    rw [hb, bsel_f]
    cases h0 : Nat.beq cd 0
    · rw [bsel_f]
      cases h1 : Nat.beq cd 1
      · rw [bsel_f]
        cases h2 : Nat.beq cd 2
        · rw [bsel_f]
          cases h3 : Nat.beq cd 3
          · rw [bsel_f]
            cases h4 : Nat.beq cd 4
            · rw [bsel_f]
              cases h6 : Nat.beq cd 6
              · rw [bsel_f]
                exact q2_good cinv_FAIL
              · rw [bsel_t]
                exact q2_good (wEndJ_good hs)
            · rw [bsel_t]
              exact q1_good (sUbs_good H hs hS)
          · rw [bsel_t]
            exact q1_good (sUfs_good H hs hS)
        · rw [bsel_t]
          exact q1_good (sEbs_good hs hS)
      · rw [bsel_t]
        exact q1_good (sEfs_good hs hS)
    · rw [bsel_t]
      exact q1_good (sNs_good H hs)

theorem endK_good {q : ℕ × St} (hq : QInv k φ x y t q) : CInv k φ t (endK q) := by
  obtain ⟨m, s⟩ := q
  rw [endK_eq, land1, shr1]
  rcases hq with ⟨hm, hx⟩ | ⟨hm, -⟩
  · rw [show Nat.beq (m % 2) 0 = true from beq_eq_true.2 hm, bsel_t]
    exact hx
  · have hb : Nat.beq (m % 2) 0 = false := by
      cases e : Nat.beq (m % 2) 0
      · rfl
      · rw [beq_eq_true.1 e] at hm
        exact absurd hm (by norm_num)
    rw [hb, bsel_f]
    exact cinv_FAIL

omit [Group G] in
theorem natRec_inv {β : Type} (P : β → Prop) (f : ℕ → (ℕ → β → β) → ℕ → β → β)
    (hf : ∀ n (ih : ℕ → β → β), (∀ r q, P q → P (ih r q)) → ∀ r q, P q → P (f n ih r q)) :
    ∀ n r q, P q → P (Nat.rec (motive := fun _ => ℕ → β → β) (fun _ q => q) f n r q)
  | 0, _, _, h => h
  | n + 1, r, q, h => hf n _ (natRec_inv P f hf n) r q h

theorem chunkK_good (H : Hyp k φ x y t) (C : ℕ) {c : ℕ} (hc : CInv k φ t c) :
    CInv k φ t (chunkK k C c) := by
  unfold chunkK
  refine endK_good (natRec_inv (QInv k φ x y t) _ ?_ _ _ _ (q2_good hc))
  intro n ih hih r q hq
  simp only [strictT_eq, forceK_eq]
  exact hih _ _ (kStep_good H _ _ hq)

theorem runK_good (H : Hyp k φ x y t) : ∀ (l : List ℕ) (c : ℕ), CInv k φ t c → CInv k φ t (runK k l c)
  | [], _, h => h
  | C :: l, c, h => by
    change CInv k φ t (strictN (chunkK k C c) (runK k l))
    rw [strictN_eq]
    exact runK_good H l _ (chunkK_good H C h)

end Facts

theorem oBase_eq (O : ℕ) : oBase O = O % 2 ^ 340 := by
  change O &&& (1 <<< 340 - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]

theorem oG_eq (O : ℕ) : oG O = O / 2 ^ 52 % 2 ^ 144 := by
  change (O >>> 52) &&& (2 ^ 144 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem oGi'_eq (O : ℕ) : oGi' O = O / 2 ^ 196 % 2 ^ 144 := by
  change (O >>> 196) &&& (2 ^ 144 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem oG_oBase (O : ℕ) : oG (oBase O) = oG O := by
  rw [oG_eq, oG_eq, oBase_eq, show (2 : ℕ) ^ 340 = 2 ^ 52 * 2 ^ 288 by norm_num,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by norm_num : (2 : ℕ) ^ 144 ∣ 2 ^ 288)]

theorem oGi_oBase (O : ℕ) : oGi (oBase O) = oGi' O := by
  change oBase O >>> 196 = _
  rw [oGi'_eq, oBase_eq, Nat.shiftRight_eq_div_pow,
    show (2 : ℕ) ^ 340 = 2 ^ 196 * 2 ^ 144 by norm_num, Nat.mod_mul_right_div_self]

theorem chkOmF_eq (TH O H h : ℕ) : chkOmF TH O H h = chkOm TH O H h := by
  cases O <;> cases H <;> rfl

theorem om_of_kPts {k : KD} (hP : kPts k = true)
    (hdr : ∀ a < 2 ^ 16, 0 < k.HT a →
      InK k.LET (hMat (k.HT a)) ∧ mul12 (hMat (k.HT a)) (hInv (k.HT a)) = ident12) :
    ∀ j < k.NOM, k.OT j ≠ 0 →
      InK k.LET (oG (k.OT j)) ∧ mul12 (oG (k.OT j)) (oGi' (k.OT j)) = ident12 := by
  intro j hj hne
  obtain ⟨-, h2⟩ := andB_eq_true.1 hP
  have hO := CFSG.Certificates.J4KShape.rngAll_spec _ h2 j (Nat.zero_le _) hj (by
    change j < 0 + 64 * ((k.NOM - 0) >>> 6 + 1)
    rw [Nat.shiftRight_eq_div_pow]
    omega)
  change orB (Nat.beq (k.OT j) 0) _ = true at hO
  rcases orB_eq_true.1 hO with h0 | hO
  · exact absurd (beq_eq_true.1 h0) hne
  obtain ⟨-, hO⟩ := andB_eq_true.1 hO
  obtain ⟨-, hO⟩ := andB_eq_true.1 hO
  rw [chkOmF_eq] at hO
  unfold chkOm at hO
  simp only [andB_eq_true, beq_eq_true] at hO
  obtain ⟨-, -, -, hm, hH⟩ := hO
  rw [oG_oBase, oGi_oBase] at hm
  rw [oG_oBase] at hH
  have hpos : 0 < k.HT (oH (k.OT j)) := by
    refine Nat.pos_of_ne_zero fun h0 => toMat_ne_zero_of_mul hm ?_
    rw [hH, h0, show hMat 0 = 0 from rfl, toMat_zero]
  refine ⟨?_, hm⟩
  rw [hH]
  exact (hdr _ (Nat.and_lt_two_pow _ (by decide)) hpos).1

theorem letB_eq (v : ℕ) (f : ℕ → Bool) : letB v f = f v := by
  cases v <;> rfl

theorem toMat_ne_zero_of_mul' {A B : ℕ} (h : mul12 A B = ident12) : toMat B ≠ 0 := by
  intro h0
  have e := congrArg toMat h
  rw [toMat_mul12, h0, mul_zero, toMat_ident12] at e
  exact zero_ne_one e

theorem khat_letter_mem {LET c : ℕ} (hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 5 ∨ c = 6) :
    lvE (jv (xh LET) (yh LET) 1 (zh LET)) c ∈ Khat LET := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ev0]
    exact Subgroup.subset_closure (by simp)
  · rw [ev1]
    exact (Khat LET).inv_mem (Subgroup.subset_closure (by simp))
  · rw [ev2]
    exact Subgroup.subset_closure (by simp)
  · rw [ev3]
    exact (Khat LET).inv_mem (Subgroup.subset_closure (by simp))
  · rw [ev5]
    exact Subgroup.subset_closure (by simp)
  · rw [ev6]
    exact (Khat LET).inv_mem (Subgroup.subset_closure (by simp))

theorem wordVal_mem {M : Type*} [Group M] {S : Subgroup M} {e : ℕ → M} {w : ℕ} :
    ∀ n : ℕ, (∀ i < n, e (wLet w i) ∈ S) → wordVal e w n ∈ S
  | 0, _ => S.one_mem
  | n + 1, h => by
    rw [wordVal_succ]
    exact S.mul_mem (wordVal_mem n fun i hi => h i (by omega)) (h n (by omega))

theorem inK_word {LET w n M : ℕ} (h01 : chkInv (letMat LET 0) (letMat LET 1) = true)
    (h23 : chkInv (letMat LET 2) (letMat LET 3) = true)
    (h56 : chkInv (letMat LET 5) (letMat LET 6) = true) (hL : LET < 2 ^ 1008)
    (h4 : letMat LET 4 = 0) (hE : chkEval LET w n M = true) (hM : toMat M ≠ 0) : InK LET M := by
  have h1 := chkEval_sound hE
  have hg : ∀ i < n, wLet w i = 0 ∨ wLet w i = 1 ∨ wLet w i = 2 ∨ wLet w i = 3 ∨ wLet w i = 5 ∨
      wLet w i = 6 := fun i hi =>
    letter_cases hL h4 fun h0 => hM (h1.trans (wordVal_eq_zero (e := fun c => toMat (letMat LET c)) hi h0))
  refine ⟨⟨_, wordVal_mem n fun i hi => khat_letter_mem (hg i hi)⟩, ?_⟩
  rw [h1, model_word_of h01 h23 h56 hg]

theorem hdr_of_kHdr {k : KD} (hS : kSetup k = true) (hH : kHdr k = true)
    (hz : ∀ a, k.nH ≤ a → a < 2 ^ 16 → k.HT a = 0) :
    ∀ a < 2 ^ 16, 0 < k.HT a →
      InK k.LET (hMat (k.HT a)) ∧ mul12 (hMat (k.HT a)) (hInv (k.HT a)) = ident12 := by
  obtain ⟨h4, h01, h23, h56, hL, -, -⟩ := kSetup_parts hS
  have hT : chkEval k.LET (wW k.PAW) (wN k.PAW) k.TR1 = true ∧
      chkEval k.LET (wW k.PBW) (wN k.PBW) k.PS1 = true := by
    unfold kSetup at hS
    simp only [andB_eq_true] at hS
    exact ⟨hS.2.2.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2.2.2.1⟩
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha16 ha
  have haN : a < k.nH := by
    by_contra hc
    rw [hz a (by omega) ha16] at ha
    exact absurd ha (lt_irrefl 0)
  have hH' : allIn 0 k.nH (hOK k.HT k.LET 7 k.TR1 k.PS1) = true := hH
  have h := CFSG.Certificates.J4KShape.rngAll_spec _ hH' a (Nat.zero_le _) haN (by
    change a < 0 + 64 * ((k.nH - 0) >>> 6 + 1)
    rw [Nat.shiftRight_eq_div_pow]
    omega)
  unfold hOK at h
  rw [letB_eq] at h
  obtain ⟨hm, hk⟩ := andB_eq_true.1 h
  have hm' : mul12 (hMat (k.HT a)) (hInv (k.HT a)) = ident12 := by
    rw [← mulF_eq]
    exact beq_eq_true.1 hm
  refine ⟨?_, hm'⟩
  have hne := toMat_ne_zero_of_mul hm'
  have pos : ∀ b, toMat (hMat (k.HT b)) ≠ 0 → 0 < k.HT b := fun b hb =>
    Nat.pos_of_ne_zero fun h0 => hb (by rw [h0, show hMat 0 = 0 from rfl, toMat_zero])
  cases h0 : Nat.beq (hKind (k.HT a)) 0 <;> simp only [h0] at hk
  · cases h1 : Nat.beq (hKind (k.HT a)) 1 <;> simp only [h1] at hk
    · cases h2 : Nat.beq (hKind (k.HT a)) 2 <;> simp only [h2] at hk
      · cases h3 : Nat.beq (hKind (k.HT a)) 3 <;> simp only [h3] at hk
        · simp only [andB_eq_true, beq_eq_true, orB_eq_true] at hk
          rcases hk.2.2 with e | e
          · rw [e] at hne ⊢
            exact inK_word h01 h23 h56 hL h4 hT.1 hne
          · rw [e] at hne ⊢
            exact inK_word h01 h23 h56 hL h4 hT.2 hne
        · simp only [andB_eq_true, beq_eq_true, blt_eq_true, mulF_eq] at hk
          have hb := toMat_ne_zero_of_mul' hk.2
          exact (ih _ hk.1 (by have := hk.1; omega) (pos _ hb)).1.of_inv' hk.2
      · simp only [andB_eq_true, beq_eq_true, blt_eq_true, mulF_eq] at hk
        obtain ⟨hAa, hBb, e⟩ := hk
        rw [e] at hne ⊢
        rw [toMat_mul12] at hne
        have hA0 : toMat (hMat (k.HT (hA (k.HT a)))) ≠ 0 := fun h' => hne (by rw [h', zero_mul])
        have hB0 : toMat (hMat (k.HT (hB (k.HT a)))) ≠ 0 := fun h' => hne (by rw [h', mul_zero])
        exact (ih _ hAa (by omega) (pos _ hA0)).1.mul (ih _ hBb (by omega) (pos _ hB0)).1
    · simp only [andB_eq_true, beq_eq_true, blt_eq_true] at hk
      obtain ⟨-, e⟩ := hk
      rw [e] at hne ⊢
      have hc := letter_cases hL h4 hne
      exact ⟨⟨_, khat_letter_mem hc⟩, (model_letter h01 h23 h56 hc).symm⟩
  · rw [beq_eq_true.1 hk]
    exact inK_ident

theorem kFacts_sound {k : KD} {KW : List ℕ} (hS : kSetup k = true) (hP : kPts k = true)
    (hRg : kRange k = true) (hK : runK k KW (mkC 0 1) = mkC k.NF k.ND)
    {G : Type*} [Group G] (φ : Khat k.LET →* G) {x y t : G}
    (hx : ∀ g : Khat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hy : ∀ g : Khat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hdr : ∀ a < 2 ^ 16, 0 < k.HT a →
      InK k.LET (hMat (k.HT a)) ∧ mul12 (hMat (k.HT a)) (hInv (k.HT a)) = ident12)
    (psi : ∀ e < 512, ∀ h τ : ℕ, τ < 2 ^ 144 → inT k.TH (lamT (k.LT e)) h τ = true →
      (InK k.LET τ ↔ InK k.LET (mul12 (lP' (k.LT e)) (Nat.land τ linMask))) ∧
      (InK k.LET τ → t * ev φ τ * t = ev φ (mul12 (lP' (k.LT e)) (Nat.land τ linMask))))
    (words : ∀ w < 2 ^ 16, wFits (wW (k.WT w)) (wN (k.WT w)) = true ∧ rv (jv x y t 1) (k.WT w) = 1) :
    FOK k k.NF ∧ ∃ w : ℕ → G, w 0 = 1 ∧ ∀ g < k.NF, FRel k φ t w g := by
  obtain ⟨-, h01, h23, -, -, -, -⟩ := kSetup_parts hS
  have H : Hyp k φ x y t := ⟨h01, h23, hx, hy, ht, hdr, om_of_kPts hP hdr, psi, fun w hw =>
    ⟨wFits_lt (words w hw).1, (rv_eq_wordVal _ _).symm.trans (words w hw).2⟩⟩
  obtain ⟨-, hR⟩ := andB_eq_true.1 hRg
  obtain ⟨hND, hR⟩ := andB_eq_true.1 hR
  obtain ⟨hNF, -⟩ := andB_eq_true.1 hR
  have hND' : k.ND < 65535 := blt_eq_true.1 hND
  have hNF' : k.NF < 1048576 := blt_eq_true.1 hNF
  have h := runK_good H KW _ cinv_init
  rw [hK] at h
  unfold CInv at h
  rw [cIdx_mkC (by omega), cNd_mkC (by omega) (by omega)] at h
  rcases h with h | ⟨-, hfok, w₀, hw0, hw⟩
  · omega
  · exact ⟨hfok, w₀, hw0, hw w₀ fun _ _ => rfl⟩

theorem kFacts_sound' {k : KD} {KW : List ℕ} (hS : kSetup k = true) (hH : kHdr k = true)
    (hP : kPts k = true) (hRg : kRange k = true) (hK : runK k KW (mkC 0 1) = mkC k.NF k.ND)
    (hz : ∀ a, k.nH ≤ a → a < 2 ^ 16 → k.HT a = 0)
    {G : Type*} [Group G] (φ : Khat k.LET →* G) {x y t : G}
    (hx : ∀ g : Khat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hy : ∀ g : Khat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (psi : ∀ e < 512, ∀ h τ : ℕ, τ < 2 ^ 144 → inT k.TH (lamT (k.LT e)) h τ = true →
      (InK k.LET τ ↔ InK k.LET (mul12 (lP' (k.LT e)) (Nat.land τ linMask))) ∧
      (InK k.LET τ → t * ev φ τ * t = ev φ (mul12 (lP' (k.LT e)) (Nat.land τ linMask))))
    (words : ∀ w < 2 ^ 16, wFits (wW (k.WT w)) (wN (k.WT w)) = true ∧ rv (jv x y t 1) (k.WT w) = 1) :
    FOK k k.NF ∧ ∃ w : ℕ → G, w 0 = 1 ∧ ∀ g < k.NF, FRel k φ t w g :=
  kFacts_sound hS hP hRg hK φ hx hy ht (hdr_of_kHdr hS hH hz) psi words

end CFSG.KJ4.KRoute

end
