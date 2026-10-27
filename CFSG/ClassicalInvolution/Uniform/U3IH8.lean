module

public import CFSG.ClassicalInvolution.Uniform.U3Thm4
public import CFSG.ClassicalInvolution.Uniform.U3Thm7
public import CFSG.ClassicalInvolution.Uniform.UBranch

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly

theorem ih8RestU_three_of (hG2D4 : Ih8G2D4EdgeU) (hThree : Ih8ThreeU) (hTwin : Ih8TwinShapeU)
    (h5 : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm5BelowU 3 1 n)
    (hMu : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → MuTableBelowU 3 1 n)
    (h3 : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm3TypedBelowExactU 3 1 n) : IH8RestU 3 1 :=
  fun n hn => ⟨h5 n hn, thm6TypedBelowU_three_of_citBelowT hn,
    thm7TypedBelowU_three_of hTwin hn, thm8TypedBelowU_three_of hG2D4 hThree hn, hMu n hn,
    h3 n hn⟩

theorem ihInterface8U_three_of_inputs (hold : IHInterface8 3) (hG2D4 : Ih8G2D4EdgeU)
    (hThree : Ih8ThreeU) (hTwin : Ih8TwinShapeU)
    (h5 : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm5BelowU 3 1 n)
    (hMu : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → MuTableBelowU 3 1 n)
    (h3 : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm3TypedBelowExactU 3 1 n) : IHInterface8U 3 :=
  ihInterface8U_three_of_rest hold ihInterfaceU_three
    (ih8RestU_three_of hG2D4 hThree hTwin h5 hMu h3)

theorem ihInterface8U_of_ih8RestU {p : ℕ} [Fact p.Prime]
    (h : ∀ e : ℕ, 3 ≤ p ^ e → IH8RestU p e) : IHInterface8U p :=
  ihInterface8U_of_rest (fun _ _ => ihInterfaceU_proved) h

end CFSG.ClassicalInvolution.Uniform
