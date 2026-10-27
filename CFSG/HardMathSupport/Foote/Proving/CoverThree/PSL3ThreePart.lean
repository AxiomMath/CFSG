module

public import CFSG.HardMathSupport.Foote.Proving.CoverThree.CentreSL3
public import CFSG.HardMathSupport.Foote.Proving.CoverThree.OrderSL3

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Proving

public theorem padicValNat_three_natCard_PSL3_of_three_cover (F : Type*) [Field F] [Fintype F]
    (h3 : 3 ∣ Fintype.card F - 1) (h9 : ¬ 9 ∣ Fintype.card F - 1) :
    padicValNat 3 (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSL := padicValNat_three_natCard_SL3_of_three_cover F h3 h9
  have hmul := natCard_PSL3_mul_gcd F
  have hgcd : Nat.gcd 3 (Fintype.card F - 1) = 3 := Nat.gcd_eq_left h3
  rw [hgcd] at hmul
  have hSLne : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) ≠ 0 := by
    intro h0
    rw [h0, padicValNat_zero_right] at hSL
    exact absurd hSL (by norm_num)
  have hPSLne : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hSLne hmul.symm
  have h3ne : (3 : ℕ) ≠ 0 := by norm_num
  have key : padicValNat 3 (Nat.card (Matrix.SpecialLinearGroup (Fin 3) F)) =
      padicValNat 3 (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) + padicValNat 3 3 := by
    conv_lhs => rw [← hmul]
    exact padicValNat.mul hPSLne h3ne
  rw [padicValNat_self] at key
  omega

end CFSG.HardMathSupport.Foote.Proving
