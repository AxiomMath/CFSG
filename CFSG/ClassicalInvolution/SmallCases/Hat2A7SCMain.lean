module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCTwin
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCAlpha

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Main


@[expose] def A7TCRes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → (∀ L ∈ Ω, ∀ J ∈ twinSet Ω L, J = L) → ¬ DEdgeless Ω → DConnected Ω →
      (∀ L ∈ Ω, ∀ z : G, IsUniqueInvolution L z → ¬ Hat2A7S8.IndepTri Ω L z) → False

theorem a7TC_of_res (hE : A7ThmE) (hR : A7TCRes) : A7TC := by
  intro G _ _ _ Ω K hs hedge hconn
  have hΩ : HypOmegaGen Ω := hs.hyp
  by_cases hT : ∃ K' ∈ twinSet Ω K, K' ≠ K
  · obtain ⟨K', h1, h2⟩ := hT
    exact false_of_twin_of_thmE hE hs h1 h2 hedge hconn
  · push Not at hT
    have hnt : ∀ L ∈ Ω, ∀ J ∈ twinSet Ω L, J = L := fun L hL =>
      T8.noTwins_of_mem hΩ.conjInvariant hs.trans hT hL
    by_cases hI : ∃ L ∈ Ω, ∃ z : G, IsUniqueInvolution L z ∧ Hat2A7S8.IndepTri Ω L z
    · obtain ⟨L, hL, z, hz, hIL⟩ := hI
      exact false_of_indepTri hs.toPre2A7 hnt hedge hconn hL hz hIL
    · push Not at hI
      exact hR G Ω K hs hnt hedge hconn fun L hL z hz => hI L hL z hz

end Main

end CFSG.ClassicalInvolution.Hat2A7S
