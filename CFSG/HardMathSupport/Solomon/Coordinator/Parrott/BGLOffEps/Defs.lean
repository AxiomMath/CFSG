module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26BGL
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def BGLOffEpsCharThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F % 3 = 0 ∧
        Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL 3 F))) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Nat.card F = q ^ 2 ∧ q % 3 = 0 ∧
        Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSU 3 q F)))) →
    ∀ f x : MulAut K, IsFieldAutThree f → f ≠ 1 → f ^ 3 = 1 →
      IsInnDiagThree x → x ≠ 1 → x ^ 3 = 1 → f * x = x * f →
        (⊤ : Subgroup K) ≤ Lemma512Ns.fixedSub x ⊔
          ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i)

@[expose] def BGLOffEpsU38 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    IsUThreeEight (K ⧸ Subgroup.center K) →
    ∀ f x : MulAut K, IsFieldAutThree f → f ≠ 1 → f ^ 3 = 1 →
      IsInnDiagThree x → x ≠ 1 → x ^ 3 = 1 → f * x = x * f →
        (⊤ : Subgroup K) ≤ Lemma512Ns.fixedSub x ⊔
          ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i)

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps
