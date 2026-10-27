module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def bConjJoin (B J : Subgroup G) : Subgroup G :=
  ⨆ x ∈ B, GLBConj x J

@[expose] def Lemma911S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M → p = 3 →
      ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        IsTwoPrimeComp (alphaOf p M ⊓ Subgroup.centralizer ({b} : Set G)) J →
          ∃ S : Subgroup G, IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
            S ≤ bConjJoin B J ∧ bConjJoin B J ≤ ⨆ j ∈ bConjJoin B J, GLBConj j S

end CFSG.LocalAnalysis.GLTheoremB
