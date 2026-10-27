module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I71
public import CFSG.HardMathSupport.Timmesfeld.DFour.Tower

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Assembly.LowTwoRank

abbrev D4Model (K : Type) [Field K] : Type := matrixProjectiveDerived (coordinateQuadPlus 4 K)

abbrev D4Img (K : Type) [Field K] : Subgroup (MulAut (D4Model K)) :=
  matrixProjectiveImage (coordinateQuadPlus 4 K)

variable {G : Type} [Group G]

@[expose] noncomputable def actHom (p : ℕ) (J : Subgroup G) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut (PSimple p J) :=
  (centerQuotientHom (PQuot p J)).comp (barAut p J)

@[expose] noncomputable def actImage (p : ℕ) (J B : Subgroup G) : Subgroup (MulAut (PSimple p J)) :=
  (B.subgroupOf (Subgroup.normalizer (J : Set G))).map (actHom p J)

@[expose] def NoTrialityAt (S : Type) [Group S] (P : Subgroup (MulAut S)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (r f : ℕ)
    (e : S ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)),
    r.Prime ∧ r ≠ 2 ∧ 1 ≤ f ∧ Nat.card K = r ^ f ∧
      P ≤ (matrixProjectiveImage (coordinateQuadPlus 4 K)).comap (MulAut.congr e).toMonoidHom

@[expose] def IsPOmegaEightPlusChar (ℓ : ℕ) (S : Type) [Group S] : Prop :=
  ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = ℓ ∧
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)

@[expose] def NoTrialityOddAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (J : Subgroup G), GLAIsBmax 3 B → IsEssential 3 B x →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) J →
    B ≤ Subgroup.normalizer (J : Set G) → IsPOmegaEightPlusOdd (PSimple 3 J) →
    NoTrialityAt (PSimple 3 J) (actImage 3 J B)

@[expose] def NoTrialityCharThreeAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (J : Subgroup G), GLAIsBmax 3 B → IsEssential 3 B x →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) J →
    B ≤ Subgroup.normalizer (J : Set G) → IsPOmegaEightPlusChar 3 (PSimple 3 J) →
    NoTrialityAt (PSimple 3 J) (actImage 3 J B)

@[expose] def NoTrialityNeThreeAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (J : Subgroup G), GLAIsBmax 3 B → IsEssential 3 B x →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) J →
    B ≤ Subgroup.normalizer (J : Set G) → IsPOmegaEightPlusOdd (PSimple 3 J) →
    ¬ IsPOmegaEightPlusChar 3 (PSimple 3 J) → NoTrialityAt (PSimple 3 J) (actImage 3 J B)

@[expose] def D4TrialityRankData : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r f : ℕ), r.Prime → r ≠ 2 → r ≠ 3 → Nat.card K = r ^ f →
    ∀ X : Subgroup (MulAut (D4Model K)), IsElemAbelian 3 X → ¬ X ≤ D4Img K →
      ∃ (X₁ : Subgroup (MulAut (D4Model K))) (F : Subgroup (D4Model K)) (z : D4Model K),
        X₁ ≤ X ∧ X₁ ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (D4Model K) = ⊥ ∧
          IsElemAbelian 3 F ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧ (∀ s ∈ F, s * z = z * s) ∧
          (∀ a ∈ X₁, a z = z) ∧ (∀ a ∈ X₁, ∀ s ∈ F, a s = s) ∧
          Nat.card X < Nat.card F * Nat.card X₁

theorem noTrialityOddAt_of_split [Finite G] (h3 : NoTrialityCharThreeAt G)
    (hne : NoTrialityNeThreeAt G) : NoTrialityOddAt G := by
  intro B x J hB hx hJ hBJ hD
  by_cases h : IsPOmegaEightPlusChar 3 (PSimple 3 J)
  · exact h3 B x J hB hx hJ hBJ h
  · exact hne B x J hB hx hJ hBJ hD h

end CFSG.LocalAnalysis.GLTheoremA
