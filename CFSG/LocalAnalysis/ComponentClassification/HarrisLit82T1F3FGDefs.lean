module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def KnownRowThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G) →
    Blueprint.Catalog (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
      Open.fusionZStar ↥(GH74.GLS.oPrimeResidual 2 G)) →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G,
      (IsTwoComponentIn L (centralizer {z}) ∨ IsSolvableTwoComponentIn L (centralizer {z})) →
      z ∈ L → InductionType 3 ↥L →
        IsChevalleyOver 3 (↥(GH74.GLS.oPrimeResidual 2 G) ⧸
            pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∨
          Nonempty (G ⧸ pPrimeCore 2 G ≃* ↥Blueprint.NativeSporadic.M11)

@[expose] def Harris82Lemma51Quat : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (τ : StatedLieTag) (n p f : ℕ),
    p.Prime → p ≠ 2 → Blueprint.LieModel X τ n p f →
    ∀ z : X, orderOf z = 2 → ∀ R : Subgroup X, R ≤ centralizer {z} →
      (R.subgroupOf (centralizer {z})).IsSubnormal → z ∈ R →
      (Nonempty (↥R ⧸ pPrimeCore 2 ↥R ≃* QuaternionGroup 2) ∨
        Nonempty (↥R ⧸ pPrimeCore 2 ↥R ≃* SL(2, ZMod 3))) →
        p ^ f = 3

@[expose] def Harris82Lemma226Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z₁ z₂ : G), orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ →
    z₁ * z₂ = z₂ * z₁ → ∀ L₁ L₂ : Subgroup G,
    IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    (IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∨
      IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) → z₂ ∈ L₂ →
    ¬ (((pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {z₁})).IsSubnormal →
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {z₁}) ∧
      GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K ∧
      centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) ∧
      ⁅K, GH74.GLS.oPrimeResidualOf 3 L₁⁆ = K ∧
      ∃ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
        center (↥K ⧸ pPrimeCore 2 ↥K)

end CFSG.ComponentClassification.HarrisLit.T1
