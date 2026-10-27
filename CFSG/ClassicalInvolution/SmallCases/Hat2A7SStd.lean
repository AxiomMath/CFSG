module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RStep
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform

section Standing


structure Pre2A7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  nonabelian : ∃ a b : G, a * b ≠ b * a
  hyp : AschTight.HypOmegaGen Ω
  classical : ∀ L ∈ Ω, ∃ z : G, Hat2A7.IsClassical2A7 ⊤ L z
  below : Hat2A7.CITBelow2A7 (Nat.card G)
  below3 : CITBelowAllT 3 (Nat.card G)
  below5 : CITBelowAllT 5 (Nat.card G)
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤

structure Std2A7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop extends Pre2A7 Ω K where
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J

@[expose] def A7T3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Pre2A7 Ω K → (∃ J ∈ Ω, ¬ AEmpty Ω J) → False

@[expose] def A7T6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → DEdgeless Ω → False

@[expose] def A7TC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → ¬ DEdgeless Ω → DConnected Ω → False

@[expose] def A7T7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → (∃ K' ∈ twinSet Ω K, K' ≠ K) → ¬ DConnected Ω → False

@[expose] def A7T8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    Std2A7 Ω K → ¬ DEdgeless Ω → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → False

end Standing

section Assembly


theorem pre2A7_conjClass {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (hK : Hat2A7.IsClassical2A7 ⊤ K z) (hB : Hat2A7.CITBelow2A7 (Nat.card G))
    (h3 : CITBelowAllT 3 (Nat.card G)) (h5 : CITBelowAllT 5 (Nat.card G)) :
    Pre2A7 (CoreAssembly.conjClass K) K where
  nonabelian := hnab
  hyp := hypOmegaGen_conjClass_of_twoElementsNormalize (t := .twoA7)
    trivial (IsClassicalMemberU.of2A7 hK)
    (IsIntrinsicU.of_not_isSolvableType MemberType.not_isSolvableType_twoA7)
    (A7Core.a7Omega5 G hnab K z hK)
  classical := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g * z * g⁻¹, ?_⟩
    have h1 := hK.conj g
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  below := hB
  below3 := h3
  below5 := h5
  mem := CoreAssembly.mem_conjClass_self K
  trans := fun J hJ => by
    obtain ⟨g, rfl⟩ := hJ
    exact ⟨g, rfl⟩
  gen := gen_conjClass K hK.mem (by
    intro h1
    have := hK.orderOf_eq_two
    rw [h1] at this
    simp at this)

theorem a7StepJ_of_branches (h3 : A7T3) (h6 : A7T6) (hC : A7TC) (h7 : A7T7) (h8 : A7T8) :
    Hat2A7R.A7StepJ := by
  intro G _ _ _ hnab K z hK hB hB3 hB5
  have hpre := pre2A7_conjClass hnab hK hB hB3 hB5
  by_cases hA : ∀ J ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) J
  · have hstd : Std2A7 (CoreAssembly.conjClass K) K := { hpre with aEmpty := hA }
    by_cases hE : DEdgeless (CoreAssembly.conjClass K)
    · exact h6 G _ K hstd hE
    · by_cases hD : DConnected (CoreAssembly.conjClass K)
      · exact hC G _ K hstd hE hD
      · by_cases hT : ∃ K' ∈ twinSet (CoreAssembly.conjClass K) K, K' ≠ K
        · exact h7 G _ K hstd hT hD
        · push Not at hT
          exact h8 G _ K hstd hE hT hD
  · push Not at hA
    exact h3 G _ K hpre hA

end Assembly

end CFSG.ClassicalInvolution.Hat2A7S
