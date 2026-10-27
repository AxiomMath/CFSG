module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)

@[expose] def Harris82Lemma51eOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (p : ℕ), p.Prime → p ≠ 2 →
    IsSimpleChevalleyOver p X → ∀ z : X, orderOf z = 2 → ∀ J : Subgroup X,
    IsTwoComponentIn J (centralizer {z}) → z ∈ J → ∀ r : ℕ, 1 ≤ r →
      ¬ IsCoverOf .POmegaOdd 3 p r 2 (↥J ⧸ pPrimeCore 2 ↥J)

@[expose] def Harris82Lemma411U1Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ^ f = 3 →
    IsCoverOf .POmegaOdd 3 p f 2 X → ∀ z ∈ center X, z ≠ 1 →
    ∀ α : MulAut X, α * α = 1 →
      (∃ x : X, x * x = 1 ∧ x ∉ center X ∧ α = MulAut.conj x) ∨
        ∃ J : Subgroup X, IsTwoComponentIn J (fixedSubgroup α) ∧ z ∈ J ∧
          ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J)

@[expose] def Harris82Lemma411U4Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → p ^ f = 3 →
    IsCoverOf .POmegaOdd 3 p f 2 X → ∀ C P : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ C → IsSylowIn 2 P C →
    ∃ V : Subgroup (MulAut X), V ≤ P ∧ P ⊓ (MulAut.conj : X →* MulAut X).range ≤ V ∧
      (∀ s ∈ P, ∀ v ∈ V, s * v * s⁻¹ ∈ V) ∧
      (∀ v ∈ V, ∀ w ∈ V, v ∉ (MulAut.conj : X →* MulAut X).range →
        w ∉ (MulAut.conj : X →* MulAut X).range → v⁻¹ * w ∈ (MulAut.conj : X →* MulAut X).range) ∧
      (∃ b ∈ P, ∀ s ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ V) ∧
      (∀ v ∈ V, v * v = 1 → v ∈ (MulAut.conj : X →* MulAut X).range) ∧
      ((∃ s ∈ P, s ∉ V) →
        ∃ x ∈ P, x ∉ (MulAut.conj : X →* MulAut X).range ∧ x * x = 1)

@[expose] def Harris82Lemma57SpinThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 G) →
    ∀ p f : ℕ, p.Prime → p ^ f = 3 → IsCoverOf .POmegaOdd 3 p f 2
      (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) →
    ∀ z : G, orderOf z = 2 → ∀ hzX : z ∈ GH74.GLS.oPrimeResidual 2 G,
    (QuotientGroup.mk (⟨z, hzX⟩ : ↥(GH74.GLS.oPrimeResidual 2 G)) :
        ↥(GH74.GLS.oPrimeResidual 2 G) ⧸ pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) ∉
      center (↥(GH74.GLS.oPrimeResidual 2 G) ⧸ pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) →
    ∀ J : Subgroup G, IsSolvableTwoComponentIn J (centralizer {z}) → z ∈ J →
      ∃ J₁ : Subgroup G,
        IsSolvableTwoComponentIn J₁ (GH74.GLS.oPrimeResidual 2 G ⊓ centralizer {z}) ∧
        J = (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ J₁ ∧
        GH74.GLS.oPrimeResidualOf 2 J = GH74.GLS.oPrimeResidualOf 2 J₁

@[expose] def Solomon74SpinSevenAsUsedThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ z : G, orderOf z = 2 → ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {z}) → z ∈ L →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L) →
    p ^ f = 3 → (L.subgroupOf (centralizer {z})).Characteristic →
    centralizer {z} ⊓ coreActionKernel L =
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ zpowers z →
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L →
    (∀ x ∈ centralizer ({z} : Set G), (∃ g : G, g * z * g⁻¹ = x) ↔ (x ∈ L ∧ orderOf x = 2)) →
    ∀ S : Sylow 2 G, ¬ (S : Subgroup G) ≤ L

end CFSG.ComponentClassification.HarrisLit.T1
