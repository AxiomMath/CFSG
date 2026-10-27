module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.LieType.HighestRoot.Defs
public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.HighestRoot
open CFSG.ClassicalInvolution.Generic (modelUniv IsFundTag)
open scoped MatrixGroups

abbrev conjSubgroup {G : Type*} [Group G] (g : G) (J : Subgroup G) : Subgroup G :=
  J.map (MulAut.conj g).toMonoidHom

structure HighestRootData (G : Type) [Group G] where
  p : ℕ
  e : ℕ
  [fact : Fact p.Prime]
  odd : p ≠ 2
  J : Subgroup G
  equivJ : Nonempty (J ≃* SL(2, GaloisField p e))
  V : Subgroup G
  V_le : V ≤ J
  V_ne : V ≠ ⊥
  V_pGroup : IsPGroup p V
  gen : pCoreOf p (normalizer (V : Set G)) ⊔ J = ⊤
  commuting : ∀ 𝒯 : Subgroup (MulAut G), IsPGroup 2 𝒯 → ∃ g : G, ∀ τ ∈ 𝒯,
    (conjSubgroup g J).map τ.toMonoidHom = conjSubgroup g J ∨
      ∀ a ∈ conjSubgroup g J, ∀ b ∈ (conjSubgroup g J).map τ.toMonoidHom, a * b = b * a

attribute [instance] HighestRootData.fact

@[expose] def SmallReeTwoMultiplierTrivial : Prop :=
  ∀ (P : Type) [Group P] [Finite P], Open.IsQuasisimple P → IsPGroup 2 (center P) →
    (∃ f : ℕ, ReeTitsModel (P ⧸ center P) .twistedG2 3 f) → center P = ⊥

structure OddLieInputs : Prop where
  gen : ∀ (t : StatedLieTag) (n p e : ℕ) [Fact p.Prime], p ≠ 2 → IsFundTag t →
    StatedLieAdmissible t n p e → (t, n) ≠ (.PSL, 2) →
    HighestRootGen (modelUniv t n p e Fact.out).D p
  cz : ∀ (t : StatedLieTag) (n p e : ℕ) [Fact p.Prime], p ≠ 2 → IsFundTag t →
    StatedLieAdmissible t n p e → (t, n) ≠ (.PSL, 2) → t ≠ .G2 →
    HighestRootCZ (modelUniv t n p e Fact.out).D (GaloisField p e)
  g2 : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → StatedLieAdmissible .G2 0 p e →
    G2InvolutionData (modelUniv .G2 0 p e Fact.out).D (GaloisField p e)
  ree : SmallReeTwoMultiplierTrivial

end CFSG.ComponentClassification.RankTwoOddLie
