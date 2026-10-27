module

public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

structure GLStanding (G : Type) [Group G] [Finite G] (m p : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  evenRank_ge : 4 ≤ evenRank G
  four_le : 4 ≤ m
  weakCoreLocal : ∀ q ∈ GLABeta (m + 1) G, GLAWeakCoreLocal G q
  beta : p ∈ GLABeta m G
  rank_eq : GLATwoLocalRank p G = m
  not_deltaZero : ¬ GLADeltaZero G p

@[expose] def Lemma91 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      ∀ b ∈ B, b ≠ 1 →
        GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ≤ M ∧
          pCoreOf 2 (M ⊓ Subgroup.centralizer ({b} : Set G)) ≤
            pCoreOf 2 (Subgroup.centralizer ({b} : Set G))

@[expose] def Lemma91ii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      ∀ b ∈ B, b ≠ 1 →
        pCoreOf 2 (M ⊓ Subgroup.centralizer ({b} : Set G)) ≤
          pCoreOf 2 (Subgroup.centralizer ({b} : Set G))

@[expose] def Lemma92 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      ∀ H : Subgroup G, H ≠ ⊤ → pCoreOf 2 M ⊔ B ≤ H → pCoreOf 2 M ≤ pCoreOf 2 H

@[expose] def Lemma94 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      ∀ D : Subgroup G, D ≤ B → IsPPlane p D → pCoreOf 2 M ≤ gammaD D ∧ gammaD D ≤ M

@[expose] def Prop98 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M : Subgroup G, IsBOneMax p B → IsPreUniquenessTwoLocal p B M →
      IsUniquenessTwoLocal p B M ∧
        ∀ D : Subgroup G, D ≤ B → IsPPlane p D → gammaStar p D = pCoreOf 2 M

@[expose] def Input19Delta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ B : Subgroup G, GLAIsBmax p B → ∀ H : Subgroup G, H ≠ ⊤ → B ≤ H →
      ∀ E : Subgroup G, E ≤ B → IsElemAbelian p E → Nat.card E = p ^ 3 →
        (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
          GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({e} : Set G))) ≤ GLAPPrimeCoreOf p H

@[expose] def Input19_1_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    ∀ H : Subgroup G, H ≠ ⊤ → ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E → 2 ≤ pRank p E →
      (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
        pCoreOf q (H ⊓ Subgroup.centralizer ({e} : Set G))) ⊓ GLAPPrimeCoreOf p H ≤ pCoreOf q H

end CFSG.LocalAnalysis.GLTheoremB
