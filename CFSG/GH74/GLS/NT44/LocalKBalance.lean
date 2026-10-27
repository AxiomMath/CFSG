module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2BalLocal

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

theorem isLocallyKBalanced_of_locBal1Two
    {T : Type} [Group T]
    (hLB : CFSG.GH74.Generic.BProg.B3.S3T2A7.LocBal1Two T)
    {k : ℕ}
    (hk : 1 ≤ k) :
    CFSG.GH74.GLS.Th2.Bal.IsLocallyKBalanced k T := by
  intro U hInn F hFk hF2
  obtain ⟨f, hfF, hf1⟩ :=
    CFSG.GH74.GLS.Th2.Bal.exists_ne_one_of_two_pow_le hk hFk
  have hf2 : orderOf f = 2 := by
    have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime (p := 2) (hp := h2)
    · rw [pow_two]
      exact hF2 f hfF
    · exact hf1
  have hle := CFSG.ClassicalInvolution.Balance.deltaCore_le_involutionOddCore hfF hf1
  rw [hLB U hInn f hf2] at hle
  exact le_bot_iff.mp hle

end CFSG.GH74.GLS.NT44

end
