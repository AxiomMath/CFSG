module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectMA

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer

variable (p f : ℕ) [Fact p.Prime]

@[expose] def LayerLieType {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (c : G)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  SectionLieType p f (exactFamily Ω c) (exactLayer Ω c) t n

@[expose] def LayerOrthType {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (c : G)
    (d : ℕ) (ε : Bool) : Prop :=
  SectionOrthType p f (exactFamily Ω c) (exactLayer Ω c) d ε

variable {p f}

section Compare

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem layerOrthType_iff_rLayer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : c * c = 1) (d : ℕ) (ε : Bool) :
    LayerOrthType p f Ω c d ε ↔ SectionOrthType p f (exactFamily Ω c) (rLayer Ω c) d ε := by
  unfold LayerOrthType
  rw [rLayer_eq_exactLayer hp hq hΩ hc2]

theorem restrictFamily_rLayer_subset (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z) (c : G) :
    restrictFamily Ω (exactLayer Ω c) ⊆ restrictFamily (exactFamily Ω c) (exactLayer Ω c) := by
  rintro _ ⟨K, hK, hKY, rfl⟩
  exact ⟨K, centMembers_subset_exactFamily hcls ⟨hK, hKY.trans (exactLayer_le_centralizer Ω c)⟩,
    hKY, rfl⟩

theorem layerOrthType_iff_of_subset (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hsub : exactFamily Ω c ⊆ Ω) (d : ℕ) (ε : Bool) :
    LayerOrthType p f Ω c d ε ↔ SectionOrthType p f Ω (exactLayer Ω c) d ε := by
  have hfam : restrictFamily (exactFamily Ω c) (exactLayer Ω c) =
      restrictFamily Ω (exactLayer Ω c) := by
    refine Set.Subset.antisymm ?_ (restrictFamily_rLayer_subset hcls c)
    rintro _ ⟨K, hK, hKY, rfl⟩
    exact ⟨K, hsub hK, hKY, rfl⟩
  unfold LayerOrthType SectionOrthType SectionLieType
  rw [hfam]

theorem layerOrthType_iff_of_exactMembers (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hex : ExactMembers Ω) (hc2 : c * c = 1) (d : ℕ) (ε : Bool) :
    LayerOrthType p f Ω c d ε ↔ SectionOrthType p f Ω (rLayer Ω c) d ε := by
  have hcls := hΩ.classical
  have hsub : exactFamily Ω c ⊆ Ω := by
    rw [exactFamily_eq_centMembers_of_exact hex hcls]
    exact fun K hK => hK.1
  rw [layerOrthType_iff_of_subset hcls hsub, rLayer_eq_exactLayer hp hq hΩ hc2]

end Compare

end CFSG.ClassicalInvolution.Asc77
