module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CyclicActor
public import CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaSemiregularity
public import CFSG.LocalAnalysis.RankThreeUC.Section5.IrreducibleConjugateGeneration

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    (⁅B, P⁆ ∈ Delta p P ρ) ∧
    (P ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ ∧
      ∀ b ∈ B, b ≠ 1 →
        P ⊓ Subgroup.centralizer ({b} : Set G) = P ⊓ Subgroup.centralizer (B : Set G)) ∧
    IsCyclic ↥B ∧
    (∀ b ∈ B, b ≠ 1 → ∀ F ∈ Delta p P ρ, F ≠ ⁅B, P⁆ →
      b ∉ Subgroup.normalizer (F : Set G)) ∧
    (∀ D₁ ∈ Delta p P ρ, ∀ D₂ ∈ Delta p P ρ,
      ∃ s ∈ twoCoreCommutator T B, D₂ = D₁.map (MulAut.conj s).toMonoidHom) ∧
    (P = Subgroup.closure
        {x : G | ∃ s ∈ twoCoreCommutator T B, x ∈ (P ⊓ Subgroup.centralizer (B : Set G)).map
          (MulAut.conj s).toMonoidHom} ∧
      ∀ P₀ : Subgroup G, P₀ ≤ P → twoCoreCommutator T B ≤ Subgroup.normalizer (P₀ : Set G) →
        B ≤ Subgroup.normalizer (P₀ : Set G) → P₀ ≠ ⊥ → P₀ = P) := by
  obtain ⟨h1, h2, -⟩ := CanonicalBFixedHyperplane.canonical hc
  exact ⟨h1, h2,
    CyclicActor.cyclic hc,
    DeltaSemiregularity.semiregular hc,
    DeltaTransitivity.transitive hc,
    IrreducibleConjugateGeneration.irreducible_generated hc⟩

end Section5
end CFSG.LocalAnalysis.RankThreeUC
