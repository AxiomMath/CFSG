module

public import Certificates.Data.Kernel.FzZ8.Z8
public import CFSG.Certificates.Kernel.FzZ8.Fusion
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef

public section

namespace CFSG.KC.FzZ8

open Certificates.FzR10A Certificates.FzR10 CFSG.OddStandard.SmallF3.FritzII
open CFSG.KC.FzUT (band fldN band_iff beq_iff blt_iff)

@[expose] def pkM (m : Mat) : Nat := m.a + 8 * m.b + 64 * m.c + 512 * m.d

theorem land_mod (x k : Nat) : Nat.land x (2 ^ k - 1) = x % 2 ^ k :=
  Nat.and_two_pow_sub_one_eq_mod x k

theorem land7 (x : Nat) : Nat.land x 7 = x % 8 := land_mod x 3

theorem land63 (x : Nat) : Nat.land x 63 = x % 64 := land_mod x 6

theorem land3 (x : Nat) : Nat.land x 3 = x % 4 := land_mod x 2

theorem land1 (x : Nat) : Nat.land x 1 = x % 2 := land_mod x 1

theorem shr_div (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

theorem pk_fld {m : Mat} (hm : FzR10AMatLt m) :
    fldN (pkM m) 3 7 0 = m.a ∧ fldN (pkM m) 3 7 1 = m.b ∧ fldN (pkM m) 3 7 2 = m.c ∧
      fldN (pkM m) 3 7 3 = m.d := by
  obtain ⟨ha, hb, hc, hd⟩ := hm
  unfold fldN pkM
  simp only [Nat.mul_eq, land7, shr_div]
  norm_num
  omega

theorem apZ_form (M p : Nat) : apZ M p = (fldN M 3 7 0 * (p % 8) + fldN M 3 7 1 * (p / 8)) % 8 +
    8 * ((fldN M 3 7 2 * (p % 8) + fldN M 3 7 3 * (p / 8)) % 8) := by
  unfold apZ
  rw [land7, shr_div]
  rfl

theorem apZ_eq {m : Mat} (hm : FzR10AMatLt m) {p : Nat} (hp : p < 64) :
    apZ (pkM m) p = m.ap p := by
  obtain ⟨h0, h1, h2, h3⟩ := pk_fld hm
  rw [apZ_form, h0, h1, h2, h3]
  unfold Mat.ap
  rw [Nat.mod_eq_of_lt (show p / 8 < 8 by omega)]

theorem ap_lt (m : Mat) (p : Nat) : m.ap p < 64 := by
  unfold Mat.ap
  omega

theorem apCZ_eq (b M q : Nat) : apCZ b M q = if b = 1 then apZ M q else q := by
  unfold apCZ
  by_cases h : b = 1
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h, CFSG.KC.FzUT.fp_beq_f h]

theorem actZ_eq {t s l : Mat} (ht : FzR10AMatLt t) (hs : FzR10AMatLt s) (hl : FzR10AMatLt l)
    {v q : Nat} (hq : q < 64) : actZ (pkM t) (pkM s) (pkM l) v q = vAct t s l v q := by
  unfold actZ vAct
  rw [apCZ_eq, apCZ_eq, apCZ_eq, land1, land1, land1, shr_div, shr_div]
  simp only [beq_iff_eq, pow_one]
  have e4 : v / 2 ^ 2 = v / 4 := by norm_num
  rw [e4]
  split_ifs <;> simp only [apZ_eq hl hq, apZ_eq hs hq, apZ_eq hs (ap_lt l q), apZ_eq ht hq,
    apZ_eq ht (ap_lt l q), apZ_eq ht (ap_lt s q), apZ_eq ht (ap_lt s _)]

theorem addZ_eq {p q : Nat} (hp : p < 64) (hq : q < 64) : addZ p q = addP p q := by
  unfold addZ addP
  rw [land7, land7, land7, land7, shr_div, shr_div]
  change (p % 8 + q % 8) % 8 + 8 * ((p / 2 ^ 3 + q / 2 ^ 3) % 8) = _
  norm_num

theorem emZ_eq {t s l : Mat} (ht : FzR10AMatLt t) (hs : FzR10AMatLt s) (hl : FzR10AMatLt l)
    {x y : Nat} (hx : x < 512) (hy : y < 512) :
    emZ (pkM t) (pkM s) (pkM l) x y = emA t s l x y := by
  unfold emZ emA
  have hv : x / 64 % 8 = x / 64 := Nat.mod_eq_of_lt (by omega)
  have hw : y / 64 % 8 = y / 64 := Nat.mod_eq_of_lt (by omega)
  rw [land63, land63, shr_div, shr_div, actZ_eq ht hs hl (Nat.mod_lt _ (by norm_num)),
    addZ_eq (Nat.mod_lt _ (by norm_num)) (ap_lt' t s l _ (Nat.mod_lt _ (by norm_num))), hv, hw]
  rfl
where
  ap_lt' (t s l : Mat) (v : Nat) {q : Nat} (hq : q < 64) : vAct t s l v q < 64 := by
    unfold vAct
    split_ifs <;> first | exact ap_lt _ _ | omega

theorem fuParA {t s l : Mat} (ht : FzR10AMatLt t) (hs : FzR10AMatLt s) (hl : FzR10AMatLt l) :
    FuParG (parOfA t s l) (emZ (pkM t) (pkM s) (pkM l)) (tlZ (pkM t)) (wZ (pkM t)) tzZ rhZ
      addZ (actZ (pkM t) (pkM s) (pkM l)) where
  he x y hx hy := (emZ_eq ht hs hl hx hy).symm
  tI := rfl
  sI := rfl
  inTL x hx := by
    change (t.ap (x % 64) == x % 64 && x / 64 % 4 == 0) = _
    unfold tlZ
    rw [land63, shr_div, land3, apZ_eq ht (Nat.mod_lt _ (by norm_num))]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, band_iff, beq_iff]
    norm_num
  inW x hx := by
    change (t.ap (x % 64) == x % 64 && decide (x / 64 < 2)) = _
    unfold wZ
    rw [land63, shr_div, apZ_eq ht (Nat.mod_lt _ (by norm_num))]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, band_iff, beq_iff, blt_iff, decide_eq_true_eq]
    norm_num
  inTZ x hx := by
    have h := (CFSG.KC.FzUT.allN_iff _ _).1 tz_check x hx
    rw [CFSG.KC.FzUT.beqB_iff] at h
    exact h.symm
  rho x hx := by
    change rho0.ap (x % 64) + 64 * (x / 64) = _
    unfold rhZ
    rw [land63, shr_div, show (3704 : Nat) = pkM rho0 from rfl,
      apZ_eq (by unfold FzR10AMatLt rho0; decide) (Nat.mod_lt _ (by norm_num))]
    norm_num
  split x y _ _ := rfl
where
  tz_check : CFSG.KC.FzUT.allN 512 (fun x => CFSG.KC.FzUT.beqB (tzZ x)
      (x / 64 == 1 && inZ (x % 64))) = true := by
    decide +kernel

end CFSG.KC.FzZ8
