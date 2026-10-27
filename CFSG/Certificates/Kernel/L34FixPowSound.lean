module

public import Certificates.Data.Kernel.L34FixPow
public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public import CFSG.Certificates.Kernel.L34W.Tab42Sound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34FixPow

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34KSnd CFSG.KC.L34W
open CFSG.PSL3Four.Native

theorem itK_eq (x k p : Nat) : itK x k p = (pg 6 (mask 6) x)^[k] p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

theorem powTab_unpack {x : Nat} (hx : Cn x) : ∀ k, ∃ y, Cn y ∧
    powTab 42 (unpack 42 6 x) k = unpack 42 6 y ∧
      ∀ p < 42, pg 6 (mask 6) y p = (pg 6 (mask 6) x)^[k] p
  | 0 => ⟨pidn 42 6, cn_pidn, idTab42, fun _ hp => pg_pidn' szOK42 hp⟩
  | k + 1 => by
    obtain ⟨y, cy, ey, py⟩ := powTab_unpack hx k
    refine ⟨pcomp 42 6 (mask 6) x y, canonK_pcomp hx cy, ?_, fun p hp => ?_⟩
    · change comp 42 (unpack 42 6 x) (powTab 42 (unpack 42 6 x) k) = _
      rw [ey, comp_unpack' hx cy]
    · rw [pg_pcomp' hx hp, py p hp, Function.iterate_succ_apply']

theorem fixPow_eq {x : Nat} (hx : Cn x) (k : Nat) :
    (powTab 42 (unpack 42 6 x) k == idTab 42) = fixPow x k := by
  obtain ⟨y, cy, ey, py⟩ := powTab_unpack hx k
  rw [ey, idTab42, beq_unpack cy cn_pidn, Bool.eq_iff_iff]
  unfold fixPow
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h p hp
    have e := py p hp
    rw [Nat.eq_of_beq_eq_true h, pg_pidn' szOK42 hp] at e
    rw [itK_eq, ← e]
    exact Nat.beq_refl p
  · intro h
    have e : y = pidn 42 6 := eq_of_pg cy cn_pidn fun p hp => by
      rw [py p hp, pg_pidn' szOK42 hp, ← itK_eq]
      exact Nat.eq_of_beq_eq_true (h p hp)
    rw [e]
    exact Nat.beq_refl _

end CFSG.KC.L34FixPow

end
