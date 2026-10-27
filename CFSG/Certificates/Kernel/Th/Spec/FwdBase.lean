
module

public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
public import CFSG.Certificates.Kernel.Th.Spec.FwdPlane
public import CFSG.Certificates.Kernel.Th.Spec.FwdRelBase
public import CFSG.Sporadic.Th.KernelInputsBase
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Max3S.BasicBase
public import CFSG.Certificates.Kernel.Th.S.HswTC
import CFSG.Certificates.Kernel.Th.Gen.Max3

@[expose] public section

namespace CFSG.KC.Th.Spec.Fwd

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Gen CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.Sporadic.Bridge CFSG.Sporadic.Th CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th.Kernel Pointwise

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

private theorem recAnd_of {P : ℕ → Bool} : ∀ n,
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

private theorem marked_iff (m r : ℕ) : marked m r = true ↔ m.testBit r = true := by
  unfold marked
  rw [Nat.blt_eq]
  have e : Nat.land m (Nat.shiftLeft 1 r) = (m.testBit r).toNat * 2 ^ r := by
    rw [show Nat.land m (Nat.shiftLeft 1 r) = m &&& (1 <<< r) from rfl, Nat.one_shiftLeft,
      Nat.and_two_pow]
  rw [e]
  cases m.testBit r <;> simp [Nat.two_pow_pos]

private theorem marked_start {k : ℕ} (h : marked 34816 k = true) : k = 11 ∨ k = 15 := by
  rw [marked_iff] at h
  have hk : k < 16 := by
    by_contra hk
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 34816 < 2 ^ 16)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
    exact absurd h (by decide)
  interval_cases k <;> first | (left; rfl) | (right; rfl) | exact absurd h (by decide)

private theorem marked_end {T x y L : ℕ} (hT : eqN T x = true) (hm : allMarked L 7 y = true)
    (hxy : x / 2048 = y) : ∀ g < 7, marked (T / 2048) (regAt L g) = true := by
  rw [CFSG.KC.Th.Max3S.eq_of_eqN hT, hxy]
  exact recAnd_of (P := fun g => marked y (regAt L g)) 7 hm

private theorem hsw_sel : ∀ k < 39, Hsw.sel k = Hsw.list.getD k 0 := by decide +kernel

end CFSG.KC.Th.Spec.Fwd

end
