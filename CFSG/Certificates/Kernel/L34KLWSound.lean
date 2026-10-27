module

public import Certificates.Data.Kernel.L34KLW
public import CFSG.Certificates.Kernel.L34NormSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeAutKSound
public import CFSG.Certificates.Kernel.L34KSound

public section

namespace CFSG.KC.L34KLW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native

variable {n w : Nat}

local notation "Cn " x:max => canonK n w (mask w) (n * w) x = true

theorem allN_eq_iff {P Q : Nat} {f g : Nat → Nat} (hP : Cn P) (hQ : Cn Q)
    (hf : ∀ i < n, pg w (mask w) P i = f i) (hg : ∀ i < n, pg w (mask w) Q i = g i) :
    allN n (fun i => Nat.beq (f i) (g i)) = true ↔ unpack n w P = unpack n w Q := by
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h
    have e : P = Q := CFSG.KC.L34KSnd.eq_of_pg hP hQ fun i hi => by
      rw [hf i hi, hg i hi]
      exact Nat.beq_eq.mp (h i hi)
    rw [e]
  · intro h i hi
    have h' : (unpack n w P)[i]! = (unpack n w Q)[i]! := congrArg (fun t : Tab => t[i]!) h
    rw [unpack_get' hi, unpack_get' hi, hf i hi, hg i hi] at h'
    exact Nat.beq_eq.mpr h'

theorem o4Pt_iff {x : Nat} (hx : Cn x) :
    o4Pt n w x = true ↔
      comp n (unpack n w x) (comp n (unpack n w x) (comp n (unpack n w x) (unpack n w x))) =
        idTab n := by
  have hsz := CFSG.KC.L34KSnd.canon_sz hx
  have h2 := canonK_pcomp hx hx
  have h3 := canonK_pcomp hx h2
  rw [CFSG.KC.L34KSnd.comp_unpack' hx hx, CFSG.KC.L34KSnd.comp_unpack' hx h2,
    CFSG.KC.L34KSnd.comp_unpack' hx h3, CFSG.KC.L34KSnd.idTab_unpack' hsz]
  refine allN_eq_iff (canonK_pcomp hx h3) (CFSG.KC.L34KSnd.canon_pidn hsz) (fun i hi => ?_)
    (fun i hi => CFSG.KC.L34KSnd.pg_pidn' hsz hi)
  rw [CFSG.KC.L34KSnd.pg_pcomp' hx hi, CFSG.KC.L34KSnd.pg_pcomp' hx hi,
    CFSG.KC.L34KSnd.pg_pcomp' hx hi]

theorem comm2Pt_iff {x y : Nat} (hx : Cn x) (hy : Cn y) :
    comm2Pt n w x y = true ↔
      comp n (unpack n w x) (comp n (unpack n w y) (unpack n w y)) =
        comp n (unpack n w y) (comp n (unpack n w y) (unpack n w x)) := by
  have hyy := canonK_pcomp hy hy
  have hyx := canonK_pcomp hy hx
  rw [CFSG.KC.L34KSnd.comp_unpack' hy hy, CFSG.KC.L34KSnd.comp_unpack' hx hyy,
    CFSG.KC.L34KSnd.comp_unpack' hy hx, CFSG.KC.L34KSnd.comp_unpack' hy hyx]
  refine allN_eq_iff (canonK_pcomp hx hyy) (canonK_pcomp hy hyx) (fun i hi => ?_)
    (fun i hi => ?_)
  · rw [CFSG.KC.L34KSnd.pg_pcomp' hx hi, CFSG.KC.L34KSnd.pg_pcomp' hy hi]
  · rw [CFSG.KC.L34KSnd.pg_pcomp' hy hi, CFSG.KC.L34KSnd.pg_pcomp' hy hi]

theorem invAPt_iff {t a : Nat} (ht : Cn t) (ha : Cn a) :
    invAPt n w t a = true ↔
      comp n (unpack n w t) (unpack n w a) =
        comp n (unpack n w a) (comp n (unpack n w a) (unpack n w t)) := by
  have hat := canonK_pcomp ha ht
  rw [CFSG.KC.L34KSnd.comp_unpack' ht ha, CFSG.KC.L34KSnd.comp_unpack' ha ht,
    CFSG.KC.L34KSnd.comp_unpack' ha hat]
  refine allN_eq_iff (canonK_pcomp ht ha) (canonK_pcomp ha hat) (fun i hi => ?_)
    (fun i hi => ?_)
  · rw [CFSG.KC.L34KSnd.pg_pcomp' ht hi]
  · rw [CFSG.KC.L34KSnd.pg_pcomp' ha hi, CFSG.KC.L34KSnd.pg_pcomp' ha hi]

theorem klEnt_spec {N : Nat} {P : Nat → Nat} {e a b M q v : Nat} {X Q Y T : Nat → Nat}
    (h : klEnt n w N P e a b X M Q Y T q v = true) (hv : v % 2 = 1) :
    c4Pt n w a b (X (v / 32)) = true ∧ (v % 32 / 8 = 3 → ∃ j < M, Q j = q ∧
      q4Pt n w N P a b (X (v / 32)) (Y j) = true ∧ tauPt n w e a b (X (v / 32)) (T j) = true) := by
  unfold klEnt at h
  have e1 : Nat.beq (Nat.mod v (nat_lit 2)) (nat_lit 1) = true := Nat.beq_eq.mpr hv
  rw [e1] at h
  dsimp only at h
  rw [CFSG.KC.L34Norm.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.L34KSnd.andB_iff.1 h
  refine ⟨h1, fun hv3 => ?_⟩
  have e2 : Nat.beq (Nat.div (Nat.mod v (nat_lit 32)) (nat_lit 8)) (nat_lit 3) = true :=
    Nat.beq_eq.mpr hv3
  rw [e2] at h2
  dsimp only at h2
  obtain ⟨j, hj, h3⟩ := CFSG.KC.L34Norm.anyN_iff.1 h2
  obtain ⟨h4, h5⟩ := CFSG.KC.L34KSnd.andB_iff.1 h3
  obtain ⟨h6, h7⟩ := CFSG.KC.L34KSnd.andB_iff.1 h5
  exact ⟨j, hj, Nat.eq_of_beq_eq_true h4, h6, h7⟩

end CFSG.KC.L34KLW

end
