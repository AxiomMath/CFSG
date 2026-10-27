module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G]

@[expose] def NaturalSectionOn (W L M : Subgroup G) (d : ℕ) : Prop :=
  ∃ (π : ↥⁅W, L⁆ →* Multiplicative (altHeart d)) (θ : ↥M →* Equiv.Perm (Fin d)),
    Function.Surjective π ∧
    π.ker = (⁅W, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅W, L⁆ ∧
    (∀ σ ∈ alternatingGroup (Fin d), ∃ l ∈ L, ∃ hl : l ∈ M, θ ⟨l, hl⟩ = σ) ∧
    SectionEquiv ⁅W, L⁆ M π θ ∧
    ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (W : Set G)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
