module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOverlap
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDefs

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

structure SectionSevenBase : Prop where
  lemma_6_3 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ i j : Fin r, ∃ h ∈ Subgroup.normalizer (D : Set G),
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j)
  theorem_6_4 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ g : G,
      rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G) →
      ∀ U : Subgroup G, U ≤ Subgroup.normalizer (D : Set G) →
        AschbacherKnownGroup.IsFourGroup U →
        ¬ ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤
          rightConjugate (Subgroup.normalizer (D : Set G)) g
  theorem_3_3 : ∀ {G : Type} [Group G] [Finite G] (H : Subgroup G) (z : G), orderOf z = 2 →
    H ≠ ⊤ → (∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) →
    (ProductUniqueContainment H z → CentralProductCentralizer H z) ∧
      (CentralProductCentralizer H z → PointHullStrongSplit H z) ∧
      (PointHullStrongSplit H z → ProductUniqueContainment H z)
  lemma_3_4 : ∀ {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (A₁ A₂ : Subgroup G),
    A₁ ≤ S → A₂ ≤ S → ⁅A₁, A₂⁆ = ⊥ → 2 ≤ pRank 2 A₁ → 2 ≤ pRank 2 A₂ →
    relStronglyClosed (overlapClosure A₁ A₂) ((A₁ : Set G) ∪ A₂)
      (overlapClosure A₁ A₂ ⊓ S) →
    relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂) (S ⊓ Subgroup.normalizer (A₁ : Set G)) →
    relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂) (S ⊓ Subgroup.normalizer (A₂ : Set G)) →
    overlapClosure A₁ A₂ = ⊤ ∨
      A₁ ≤ A₂ ∨ A₂ ≤ A₁ ∨
      ((∃ g : G, rightConjugate A₁ g = A₂) ∧
        (AschbacherTheorem3.IsDihedralTwoGroup A₁ ∨ AschbacherTheorem3.IsSemidihedralTwoGroup A₁) ∧
        Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
  theorem_3 : AschbacherTheorem3.Theorem3Statement
  knownGroups : AschbacherKnownGroup.AschbacherKnownGroupFacts

structure SectionSevenInputs : Prop extends SectionSevenBase where
  lemma_7_4_dihedral : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ t g : G, t ∈ Subgroup.normalizer (D : Set G) →
      orderOf t = 2 → g ∉ Subgroup.normalizer (D : Set G) →
      (∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
        (aschbacherThm5Preimage D (Abar j)) (g * t * g⁻¹)) →
      (∀ k : Fin r, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
        aschbacherThm5Preimage D (Abar k)) →
      ∀ k : Fin r, IsSimpleGroup (Abar k) ∧ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)
  lemma_8_2 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → r = 2

end CFSG.ComponentClassification.AschbacherTheorem5
