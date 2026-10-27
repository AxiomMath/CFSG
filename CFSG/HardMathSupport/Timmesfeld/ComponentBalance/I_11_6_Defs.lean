module

public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def Kernel11_2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → ∀ B : Subgroup X, IsElemAbelian p B →
      GLATwoLocalRank p X ≤ pRank p B → ∀ L : Subgroup X, GLAPComponent p ⊤ L →
        ¬ B ≤ Subgroup.normalizer (L : Set X) →
          (Subgroup.normalizer (L : Set X)).relIndex B = p ∧
            ∀ b ∈ B, b ∉ Subgroup.normalizer (L : Set X) →
              IsSimpleGroup ↥(GLAPLayer p
                (Subgroup.centralizer ({b} : Set X) ⊓ ⨆ g ∈ B, GLBConj g L))

@[expose] def Input11_6Reduced : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → ∀ B : Subgroup X, IsSCp p ⊤ B → GLATwoLocalRank p X ≤ pRank p B →
      ∀ Y : Subgroup X, Nat.Coprime p (Nat.card Y) → B ≤ Subgroup.normalizer (Y : Set X) →
        ∀ L : Subgroup X, GLAPComponent p ⊤ L → Y ≤ Subgroup.normalizer (L : Set X)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
