module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def IsLThreeEvenExc (Q : Type) [Group Q] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Even (Nat.card F) ∧
      (Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7) ∧ Nonempty (Q ≃* ↥(StatedSL 3 F))) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Even q ∧ Nat.card F = q ^ 2 ∧
      (q % 9 = 2 ∨ q % 9 = 5) ∧ Nonempty (Q ≃* ↥(StatedSU 3 q F))

@[expose] def T158NormCat : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    (CFSG.HardMathSupport.Solomon.LocalBalance.IsLTwoOddPow Q ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsHatSix Q ∨
      CFSG.LocalAnalysis.GLTheoremB.IsHatSeven Q ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsHatMTwentyTwo Q ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsSLThreeExc Q ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsSUThreeExc Q) →
    catalogIs (Q ⧸ Subgroup.center Q) (t158Shape 3) → IsLThreeEvenExc Q

@[expose] def T158NormL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X) (x₁ x₂ : X) (L₁ L₂ : Subgroup X),
    T158Hyp 3 K B x₁ x₂ L₁ L₂ →
    InnDiagOn 3 (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) K → IsLThreeEvenExc (PQuot 3 K) → False

end CFSG.LocalAnalysis.GLTheoremA.T158

end
