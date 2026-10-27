module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameChain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer

section Core

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

structure ChainFrameCore (Ω : Set (Subgroup G)) (K J K' : Subgroup G) (z t z' : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  noTwins : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M
  below : CITBelowU p f (Nat.card G)
  frame : ChainFrameData Ω K J K' z t z'

end Core

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem ChainFrameCore.nonabelian (hs : ChainFrameCore p f Ω K J K' z t z') :
    ∃ x y : G, x * y ≠ y * x := by
  obtain ⟨z₀, hz₀⟩ := hs.hyp.classical K hs.frame.mem
  exact exists_noncomm_of_isClassicalMember hz₀

end Basic

end CFSG.ClassicalInvolution.Asc77
