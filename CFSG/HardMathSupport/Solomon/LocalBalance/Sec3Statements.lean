module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Lemma33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B : Subgroup G, GLAIsBmax p B → IsSCp p ⊤ B → ∀ b ∈ B, b ≠ 1 →
      ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
        ¬ IsStronglyLocallyOneBalanced p B b L → B ≤ Subgroup.normalizer (L : Set G) →
        ∀ x ∈ B, x ≠ 1 → ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf p L →
          GLAPLayer p (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ lambdaOf p B x

end CFSG.HardMathSupport.Solomon.LocalBalance
