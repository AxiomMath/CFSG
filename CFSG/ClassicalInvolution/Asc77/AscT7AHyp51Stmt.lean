module

public import CFSG.ClassicalInvolution.Asc77.AscT7ABasic
public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

structure TwinFrameSetting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  aEmpty : ∀ M ∈ Ω, AEmpty Ω M
  trans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M
  below : CITBelowU p f (Nat.card G)
  thm7 : Thm7TypedBelow p f (Nat.card G)
  frame : TwinFrameData Ω K K' z u J t

@[expose] def TwinFrameHyp51z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSetting p f Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) z

@[expose] def TwinFrameHyp51t : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSetting p f Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) t ∧ Hyp51At (Subgroup.closure {z, u, t}) (t * z)

@[expose] def TwinFrameHyp51u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSetting p f Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) u ∧ Hyp51At (Subgroup.closure {z, u, t}) (u * z) ∧
        Hyp51At (Subgroup.closure {z, u, t}) (u * t) ∧
          Hyp51At (Subgroup.closure {z, u, t}) (u * t * z)

@[expose] def TwinFrameHyp51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSetting p f Ω K K' J z u t →
      Hyp51 (Subgroup.closure {z, u, t})

structure TwinFrameSettingCore {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  trans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M
  below : CITBelowU p f (Nat.card G)
  thm7 : Thm7TypedBelow p f (Nat.card G)
  frame : TwinFrameData Ω K K' z u J t

@[expose] def TwinFrameHyp51zCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSettingCore p f Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) z

@[expose] def TwinFrameHyp51tCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSettingCore p f Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) t ∧ Hyp51At (Subgroup.closure {z, u, t}) (t * z)

@[expose] def TwinFrameHyp51uCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSettingCore p f Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) u ∧ Hyp51At (Subgroup.closure {z, u, t}) (u * z) ∧
        Hyp51At (Subgroup.closure {z, u, t}) (u * t) ∧
          Hyp51At (Subgroup.closure {z, u, t}) (u * t * z)

@[expose] def TwinFrameHyp51Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSettingCore p f Ω K K' J z u t →
      Hyp51 (Subgroup.closure {z, u, t})

variable {p f}

theorem TwinFrameSetting.toCore {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' J : Subgroup G} {z u t : G} (hs : TwinFrameSetting p f Ω K K' J z u t) :
    TwinFrameSettingCore p f Ω K K' J z u t :=
  ⟨hs.odd, hs.five, hs.hyp, hs.trans, hs.below, hs.thm7, hs.frame⟩

end CFSG.ClassicalInvolution.Asc77
