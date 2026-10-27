module

public import CFSG.ClassicalInvolution.Asc77.WP2Interface
public import CFSG.ClassicalInvolution.SmallCases.DSplitBranch

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

structure AscStand {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  below : CITBelowAll p (Nat.card G)
  ih : IH8All p (Nat.card G)
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤

@[expose] def ConclusionD (G : Type) [Group G] : Prop :=
  CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def ConcOrTF4 (G : Type) [Group G] : Prop :=
  ConclusionD G ∨ TwoSubgroupsFourGenerated G

theorem ConcOrTF4.conclusionD {G : Type} [Group G] (h : ConcOrTF4 G)
    (hn : ¬ TwoSubgroupsFourGenerated G) : ConclusionD G :=
  h.resolve_right hn

@[expose] def Thm6A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → DEdgeless Ω → ConcOrTF4 G

@[expose] def Thm7A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → (∃ K' ∈ twinSet Ω K, K' ≠ K) → ¬ DConnected Ω → ConcOrTF4 G

@[expose] def Thm8A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → ¬ DEdgeless Ω → (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → False

@[expose] def HypOmegaModD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → HypOmegaMod p f (CoreAssembly.conjClass K)

@[expose] def ExactD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → ExactMembers (CoreAssembly.conjClass K)

@[expose] def HypOmegaD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → HypOmega p f (CoreAssembly.conjClass K)

@[expose] def AEmptyD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → ∀ J ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) J

@[expose] def IHAllD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → CITBelowAll p (Nat.card G)

@[expose] def IHInterface8 : Prop :=
  ∀ n : ℕ, CITBelowAll p n → IH8All p n

@[expose] def AscStandOfBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → AscStand p f (CoreAssembly.conjClass K) K

variable {p f}

theorem conjInvariant_conjClass {G : Type} [Group G] (K : Subgroup G) :
    ConjInvariant (CoreAssembly.conjClass K) := by
  rintro n _ ⟨g, rfl⟩
  exact ⟨n * g, by simp only [conjSub_mul]⟩

theorem gen_conjClass {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) {z : G}
    (hz : z ∈ K) (hz1 : z ≠ 1) : (⨆ J ∈ CoreAssembly.conjClass K, J) = ⊤ := by
  have hnorm := omegaGen_normal (conjInvariant_conjClass K)
  have hK : K ≤ omegaGen (CoreAssembly.conjClass K) :=
    le_omegaGen (CoreAssembly.mem_conjClass_self K)
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact absurd (hK hz) (by rw [h]; simpa using hz1)
  · exact h

theorem hypOmegaD_of (hm : HypOmegaModD p f) (he : ExactD p f) : HypOmegaD p f :=
  fun G _ _ _ K z h => (hm G K z h).toExact (he G K z h)

theorem ascStandOfBranch_of (hΩ : HypOmegaModD p f) (hA : AEmptyD p f) (hall : IHAllD p f)
    (hih : IHInterface8 p) : AscStandOfBranch p f := by
  intro G _ _ _ K z h
  exact
    { odd := h.odd
      five := h.five
      hyp := hΩ G K z h
      below := hall G K z h
      ih := hih _ (hall G K z h)
      aEmpty := hA G K z h
      mem := CoreAssembly.mem_conjClass_self K
      trans := fun J hJ => by
        obtain ⟨g, rfl⟩ := hJ
        exact ⟨g, rfl⟩
      gen := gen_conjClass K h.member.mem (by
        intro h1
        have := h.member.orderOf_eq_two
        rw [h1] at this
        simp at this) }

end CFSG.ClassicalInvolution.Asc77
