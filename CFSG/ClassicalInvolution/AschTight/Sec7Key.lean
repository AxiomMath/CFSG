module

public import CFSG.ClassicalInvolution.Asc77.WP2Thompson

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Family

variable {G : Type} [Group G]

@[expose] def KeyOn (Ω : Set (Subgroup G)) : Prop :=
  ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W

@[expose] def RCommute (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∀ R ∈ RSet Ω, ∀ R' ∈ RSet Ω, R ≤ (S : Subgroup G) → R' ≤ (S : Subgroup G) →
    R ≠ R' → Commutes R R'

@[expose] def EtaActsR (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Sylow 2 G, ∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) →
    ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) → ∀ r ∈ R, ∀ V ∈ η, conjSub r V ∈ η

end Family

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L7_1Key : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω → KeyOn Ω

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
