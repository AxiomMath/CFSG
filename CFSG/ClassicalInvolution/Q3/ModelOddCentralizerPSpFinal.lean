module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSpComplex
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSpAdapted
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSp

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

theorem spComplexOddFree_of_card_eq_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    {n : ℕ} (hn : 2 ≤ n) : SpComplexOddFree F n := by
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  intro g hg
  obtain ⟨Q, hQ⟩ := exists_conj_gComplex g hg
  refine oddCoreIn_centralizer_eq_bot_of_equiv (MulAut.conj Q⁻¹ : StatedSp n F ≃* StatedSp n F) g ?_
  have h1 : (MulAut.conj Q⁻¹ : StatedSp n F ≃* StatedSp n F) g = gComplex n := by
    rw [MulAut.conj_apply, inv_inv, mul_assoc, hQ, inv_mul_cancel_left]
  rw [h1]
  exact oddCoreIn_centralizer_gComplex_eq_bot hn

theorem simpleOddCentralizerFreeTag_PSp : SimpleOddCentralizerFreeTag .PSp :=
  simpleOddCentralizerFreeTag_PSp_of_complex fun n hn => by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact spComplexOddFree_of_card_eq_three (by simpa using GaloisField.card 3 1 one_ne_zero) hn

end CFSG.ClassicalInvolution.Q3
