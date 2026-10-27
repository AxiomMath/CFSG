module

public import CFSG.ClassicalInvolution.Asc77.AscT7BAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

structure Hyp22Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G) : Prop where
  stand : AscStand p f Ω K
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  perp : KPerp Ω K = twinSet Ω K
  hK₃ : K₃ ∈ twinSet Ω K
  hK₃K : K₃ ≠ K
  hK₃K' : K₃ ≠ K'
  hu₁ : u₁ ∈ K ∧ orderOf u₁ = 4
  hu₂ : u₂ ∈ K' ∧ orderOf u₂ = 4
  hu₃ : u₃ ∈ K₃ ∧ orderOf u₃ = 4
  hB : IsElemAbelian2 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) 3

@[expose] def Hyp22Hyp51z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) z

@[expose] def Hyp22Hyp51u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ c ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), c ≠ 1 → c ≠ z →
        Hyp51At (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) c

variable {p f}

theorem Hyp22.setting {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃) :
    Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ where
  stand := h.std.stand
  hz := h.std.hz
  hK' := h.std.hK'
  hne := h.std.hne
  perp := h.perp
  hK₃ := h.hK₃
  hK₃K := h.hK₃K
  hK₃K' := h.hK₃K'
  hu₁ := h.hu₁
  hu₂ := h.hu₂
  hu₃ := h.hu₃
  hB := h.hB

theorem c22_2_of (hz : Hyp22Hyp51z p f) (hu : Hyp22Hyp51u p f) : C22_2 p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h
  have hs := h.setting
  have hB : Hyp51 (Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G)) := by
    refine ⟨h.isElemAbelian_B, h.natCard_B, fun c hc hc1 => ?_⟩
    by_cases hcz : c = z
    · rw [hcz]
      exact hz G Ω K K' K₃ z u₁ u₂ u₃ hs
    · exact hu G Ω K K' K₃ z u₁ u₂ u₃ hs c hc hc1 hcz
  exact lemma54_odd_and_eq hB h.closure_12_le h.isElemAbelian2_closure

end CFSG.ClassicalInvolution.Asc77
