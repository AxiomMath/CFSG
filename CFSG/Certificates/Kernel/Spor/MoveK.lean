module

public import CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.MoveK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def diffK (f g : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun k ih => nIf(Nat.beq (f k) (g k), ih, k)) n

@[expose] noncomputable def difK (f g : Nat → Nat) (n : Nat) : Bool :=
  strictB (diffK f g n) fun w => bAnd(Nat.blt w n, !(Nat.beq (f w) (g w)))

theorem difK_spec {f g : Nat → Nat} {n : Nat} (h : difK f g n = true) :
    ∃ w < n, f w ≠ g w := by
  unfold difK at h
  rw [Raw.Orb.strictB_eq, bAnd_iff, Nat.blt_eq, Bool.not_eq_true', Bool.eq_false_iff] at h
  refine ⟨_, h.1, fun e => h.2 (by rw [e]; exact Nat.beq_refl _)⟩

end CFSG.KS.MoveK

end
