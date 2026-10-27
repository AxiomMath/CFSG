module

public import CFSG.ClassicalInvolution.Uniform.U7Comm
public import CFSG.ClassicalInvolution.Uniform.U7Lie
public import CFSG.ClassicalInvolution.Uniform.U7Cent

public section

namespace CFSG.ClassicalInvolution.Uniform


theorem thm3TypedBelowExactU_three (hgen : G2NonToralGenerate3) (hF : G2CentralizerInvolution3)
    {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) : Thm3TypedBelowExactU 3 1 n :=
  ⟨thm3CommBelowExactU_three hgen hF hn, thm3LieBelowExactU_three hgen hn⟩

theorem thm3_of_g2Facts (hgen : G2NonToralGenerate3) (hF : G2CentralizerInvolution3) :
    ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm3TypedBelowExactU 3 1 n :=
  fun _ hn => thm3TypedBelowExactU_three hgen hF hn

theorem thm3TypedBelowExactU_three_of_g2NonToral (hgen : G2NonToralGenerate3) {n : ℕ}
    (hn : CITBelowT (.sl2 3 1) n) : Thm3TypedBelowExactU 3 1 n :=
  thm3TypedBelowExactU_three hgen g2CentralizerInvolution3_proved hn

theorem thm3_of_g2NonToral (hgen : G2NonToralGenerate3) :
    ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm3TypedBelowExactU 3 1 n :=
  thm3_of_g2Facts hgen g2CentralizerInvolution3_proved

end CFSG.ClassicalInvolution.Uniform
