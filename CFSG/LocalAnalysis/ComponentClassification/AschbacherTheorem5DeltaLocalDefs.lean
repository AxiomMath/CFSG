module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveOrbit
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

variable {G : Type} [Group G]

@[expose] def fourGroupsInto (H K : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ H ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
    ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ K}

@[expose] def deltaConjugates (H : Subgroup G) : Set (Subgroup G) :=
  {K | ∃ g : G, K = rightConjugate H g ∧ K ≠ H ∧ (fourGroupsInto H K).Nonempty}

@[expose] def factorZStar (D : Subgroup G) {r : ℕ}
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) (i : Fin r) : Subgroup G :=
  aschbacherThm5Preimage D (Abar i) ⊓ SectionSix.centralizing D (Abar i)

theorem mem_fourGroupsInto_iff (H K U : Subgroup G) :
    U ∈ fourGroupsInto H K ↔ U ≤ H ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
      ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ K := Iff.rfl

theorem mem_deltaConjugates_iff (H K : Subgroup G) :
    K ∈ deltaConjugates H ↔
      ∃ g : G, K = rightConjugate H g ∧ K ≠ H ∧ (fourGroupsInto H K).Nonempty := Iff.rfl

theorem deltaConjugates_eq_empty_iff (H : Subgroup G) :
    deltaConjugates H = ∅ ↔ ∀ g : G, rightConjugate H g ≠ H → ∀ U : Subgroup G, U ≤ H →
      IsElemAbelian 2 U → Nat.card U = 4 →
        ¬ ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ rightConjugate H g := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h g hg U hUH hU hU4 hcent
    exact h _ ⟨g, rfl, hg, U, hUH, hU, hU4, hcent⟩
  · rintro h K ⟨g, rfl, hg, U, hUH, hU, hU4, hcent⟩
    exact h g hg U hUH hU hU4 hcent

structure DeltaDatum (D : Subgroup G) {r : ℕ}
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) (a : Fin r) where
  g : G
  ne : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G)
  U : Subgroup G
  four : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
    (rightConjugate (Subgroup.normalizer (D : Set G)) g)
  T : Subgroup G
  sylowT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
    Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G))
  S : Subgroup G
  sylowS : IsSylowOf 2 S (aschbacherThm5Preimage D (Abar a))
  invariant : T ≤ Subgroup.normalizer (S : Set G)
  sylowInter : IsSylowOf 2 (S ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (aschbacherThm5Preimage D (Abar a) ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) g)

end CFSG.ComponentClassification.AschbacherTheorem5
