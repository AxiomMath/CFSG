
module

public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase
public import CFSG.Sporadic.Th.KernelInputsBase
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Max3S.BasicBase
public import CFSG.Certificates.Kernel.Th.S.HswTC
import CFSG.Certificates.Kernel.Th.Gen.Max3

@[expose] public section

namespace CFSG.KC.Th.Spec.FwdExt

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Gen CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.Sporadic.Bridge CFSG.Sporadic.Th CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th.Kernel Pointwise

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem recAnd_of {P : ℕ → Bool} : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (P k)) n) = true →
      ∀ k < n, P k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun k ih => andB ih (P k)) n) (P n) =
        true := h
    by_cases hkn : k = n
    · subst hkn
      exact andB_right h'
    · exact recAnd_of n (andB_left h') k (by omega)

theorem hsw_sel : ∀ k < 39, Hsw.sel k = Hsw.list.getD k 0 := by decide +kernel

end CFSG.KC.Th.Spec.FwdExt

end
