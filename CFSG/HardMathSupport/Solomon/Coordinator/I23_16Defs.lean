module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26BGL
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

@[expose] def Input23_16Three : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ∀ (B : Type) [Group B] [Finite B] (ρ : B →* MulAut K),
      IsElemAbelian 3 (⊤ : Subgroup B) →
      (∃ H : Subgroup B, Nat.card B = 3 * Nat.card H ∧ ∀ h ∈ H, IsFieldAutThree (ρ h)) →
      (⊤ : Subgroup K) ≤ ⨆ (E : Subgroup B)
        (_ : CFSG.Open.pRank 3 (⊤ : Subgroup B) - 1 ≤ CFSG.Open.pRank 3 E), fixedSubgroup ρ E

@[expose] def BGLFieldGenerationWithXThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ∀ f x : MulAut K, IsFieldAutThree f → f ≠ 1 → f ^ 3 = 1 →
      IsInnDiagThree x → x ≠ 1 → x ^ 3 = 1 → f * x = x * f →
        (⊤ : Subgroup K) ≤ Lemma512Ns.fixedSub x ⊔
          ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i)

@[expose] def BGLFieldGenerationWithXOffEps : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    ¬ IsLThreeEpsBar (K ⧸ Subgroup.center K) →
    ∀ f x : MulAut K, IsFieldAutThree f → f ≠ 1 → f ^ 3 = 1 →
      IsInnDiagThree x → x ≠ 1 → x ^ 3 = 1 → f * x = x * f →
        (⊤ : Subgroup K) ≤ Lemma512Ns.fixedSub x ⊔
          ⨆ (i : ℕ) (_ : i < 3), Lemma512Ns.fixedSub (f * x ^ i)

@[expose] def Field3Structure : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → IsThreeType K →
    (∀ α : MulAut K, α ^ 3 = 1 → IsInnDiagThree α ∨ IsFieldAutThree α) ∧
    (∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → (∀ α ∈ E, IsFieldAutThree α) →
      Nat.card E ≤ 3)

end CFSG.HardMathSupport.Solomon.Coordinator
