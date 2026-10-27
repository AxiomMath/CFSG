module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def dQ (K : Subgroup G) : Subgroup G :=
  CFSG.HardMathSupport.Solomon.LocalBalance.centralizerQuot K (GLAPPrimeCoreOf 3 K)

omit [Finite G] in
theorem mem_dQ {K : Subgroup G} {g : G} :
    g ∈ dQ K ↔ g ∈ Subgroup.normalizer (K : Set G) ∧
      g ∈ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) ∧
      ∀ y ∈ K, y * g * y⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 K := Iff.rfl

@[expose] noncomputable def gammaOneBelow (B K : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ B ∧ pRank 3 B - 1 ≤ pRank 3 E), K ⊓ Subgroup.centralizer (E : Set G)

@[expose] noncomputable def gammaLBelow (B K : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ B ∧ pRank 3 B - 1 ≤ pRank 3 E),
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set G))

@[expose] noncomputable def gammaClBelow (B K : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ B ∧ pRank 3 B - 1 ≤ pRank 3 E),
    GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer (E : Set G)) ⊔
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set G))

@[expose] def IsThreeOnePlusFour (P : Type*) [Group P] : Prop :=
  Nat.card P = 3 ^ 5 ∧ (∀ g : P, g ^ 3 = 1) ∧ Nat.card (Subgroup.center P) = 3 ∧
    ∀ a b : P, ⁅a, b⁆ ∈ Subgroup.center P

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
