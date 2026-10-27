module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

@[expose] def IsLThreeEpsBar (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 ≠ 0 ∧
      Nonempty (Y ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 ≠ 0 ∧ q ≠ 8 ∧
      Nonempty (Y ≃* StatedProj (StatedSU 3 q K)))

@[expose] def IsUThreeEight (Y : Type*) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 8 ^ 2 ∧ Nonempty (Y ≃* StatedProj (StatedSU 3 8 K))

@[expose] def BGLFieldPairGeneration : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsLThreeEpsBar (K ⧸ Subgroup.center K) → ∀ b x : MulAut K,
      IsFieldAutThree b → b ≠ 1 → b ^ 3 = 1 → IsInnDiagThree x → x ≠ 1 → x ^ 3 = 1 →
        b * x = x * b →
          (⊤ : Subgroup K) ≤
            GLAPLayer 3 (Lemma512Ns.fixedSub b) ⊔ GLAPLayer 3 (Lemma512Ns.fixedSub (b * x))

end CFSG.HardMathSupport.Solomon.Coordinator
