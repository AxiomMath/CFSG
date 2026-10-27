module

public import Certificates.Data.Kernel.Spor.MulHF
public import CFSG.Certificates.Kernel.Spor.HKeyUSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PF

theorem hsortPtKF_eq (n w cnt : Nat) (T HS HSI : Nat → Nat) (i : Nat) :
    hsortPtKF n w (mask w) cnt T HS HSI i = hsortPtK n w (mask w) cnt T HS HSI i := by
  unfold hsortPtKF hsortPtK
  simp only [strictB_eqP, hkeyU_eq]

theorem eq22_pcomp {n w : Nat} (p q : Nat) (hn : n < 2 ^ 32) (hw : 0 < w) :
    eq22 n w (mask w) p q q p = Nat.beq (pcomp n w (mask w) p q) (pcomp n w (mask w) q p) := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    unfold eq22 at h
    have e : pcomp n w (mask w) p q = pcomp n w (mask w) q p :=
      eq_of_fields hw (pcomp_shr p q hn hw) (pcomp_shr q p hn hw) fun i hi => by
        rw [pg_pcomp hn hi, pg_pcomp hn hi]
        exact Nat.eq_of_beq_eq_true (allN_spec h i hi)
    rw [e]
    exact Nat.beq_refl _
  · intro h
    have e := Nat.eq_of_beq_eq_true h
    unfold eq22
    exact allN_of_forall fun i hi => by
      rw [← pg_pcomp hn hi, ← pg_pcomp hn hi, e]
      exact Nat.beq_refl _

theorem eq2_pcomp {n w : Nat} (t a : Nat) (hn : n < 2 ^ 32) (hw : 0 < w)
    (ht : t >>> (n * w) = 0) :
    eq2 n w (mask w) t a a = Nat.beq (pcomp n w (mask w) a a) t := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    unfold eq2 at h
    have e : pcomp n w (mask w) a a = t :=
      eq_of_fields hw (pcomp_shr a a hn hw) ht fun i hi => by
        rw [pg_pcomp hn hi]
        exact (Nat.eq_of_beq_eq_true (allN_spec h i hi)).symm
    rw [e]
    exact Nat.beq_refl _
  · intro h
    have e := Nat.eq_of_beq_eq_true h
    unfold eq2
    exact allN_of_forall fun i hi => by
      rw [← pg_pcomp hn hi, e]
      exact Nat.beq_refl _

end CFSG.KS.MulH

end
