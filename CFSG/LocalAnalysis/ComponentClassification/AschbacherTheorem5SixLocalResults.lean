module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

structure SectionSixLocalResults : Prop where
  lemma_6_5_one : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ {g : G},
    rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G) →
    ∀ {U : Subgroup G}, U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g) →
    ∀ i : Fin r, U ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)
  lemma_6_5_two : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ {g : G},
    rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) →
    ∀ i : Fin r, ∃ x ∈ aschbacherThm5Preimage D (Abar i) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g,
      x ∉ factorZStar D Abar i ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1
  lemma_6_6 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → (deltaConjugates (Subgroup.normalizer (D : Set G))).Nonempty →
    ∀ i : Fin r, 2 ≤ pRank 2 (aschbacherThm5Preimage D (Abar i))
  lemma_6_7 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ {g : G},
    rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G)) →
    ∀ i : Fin r,
      2 ≤ pRank 2 (rightConjugate (aschbacherThm5Preimage D (Abar i)) g ⊓
        Subgroup.normalizer (D : Set G)) ∧
      2 ≤ pRank 2 (aschbacherThm5Preimage D (Abar i) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) g) ∧
      ∃ U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
        (rightConjugate (Subgroup.normalizer (D : Set G)) g),
        U ≤ rightConjugate (aschbacherThm5Preimage D (Abar i)) g
  lemma_6_8 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ {a : Fin r} (d : DeltaDatum D Abar a),
    2 ^ (Nat.card (aschbacherThm5Preimage D (Abar a) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) :
        Subgroup G)).factorization 2 ≤ Nat.card d.T →
    ∃ x ∈ aschbacherThm5Preimage D (Abar a),
      x ∉ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) ∧
      Even (Nat.card (d.T ⊓ rightConjugate d.T x : Subgroup G)) ∧
      rightConjugate (factorZStar D Abar a) d.g ⊓
        rightConjugate (factorZStar D Abar a) (d.g * x) ≠ ⊥
  lemma_6_9 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → (deltaConjugates (Subgroup.normalizer (D : Set G))).Nonempty →
    r = 2
  lemma_6_10 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)},
    Counterexample G D r Abar → ∀ {a : Fin r} (d : DeltaDatum D Abar a),
    ¬ aschbacherThm5Preimage D (Abar a) ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g ≤
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) →
    ¬ d.T ≤ rightConjugate (factorZStar D Abar a) d.g →
    ∃ y ∈ d.S ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g,
      (∃ b, b ≠ a ∧ rightConjugate (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g) y =
        rightConjugate (aschbacherThm5Preimage D (Abar b)) d.g) ∧
      (d.T ⊔ rightConjugate d.T y) ⊓ d.S ≠ ⊥ ∧
      (d.T ⊔ rightConjugate d.T y) ⊓ d.S ≤
        AschbacherTheorem3.centerOf (d.T ⊔ rightConjugate d.T y) ∧
      (d.T ⊔ rightConjugate d.T y) ⊓ d.S ⊔ d.T = d.T ⊔ rightConjugate d.T y ∧
      IsMulCommutative (d.T ⊔ rightConjugate d.T y : Subgroup G)

end CFSG.ComponentClassification.AschbacherTheorem5
