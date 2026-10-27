module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7P1Th
public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Stand

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}


theorem Std2A7.of_mem (h : Std2A7 Ω K) (hJ : J ∈ Ω) : Std2A7 Ω J :=
  { h with
    mem := hJ
    trans := fun L hL => by
      obtain ⟨g, hg⟩ := h.trans L hL
      obtain ⟨g₀, hg₀⟩ := h.trans J hJ
      refine ⟨g * g₀⁻¹, ?_⟩
      rw [← hg₀, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one, hg] }

theorem Std2A7.conj (h : Std2A7 Ω K) (n : G) : Std2A7 Ω (conjSub n K) :=
  { h with
    mem := h.hyp.conjInvariant n K h.mem
    trans := fun L hL => by
      obtain ⟨g, hg⟩ := h.trans L hL
      refine ⟨g * n⁻¹, ?_⟩
      rw [← conjSub_mul, inv_mul_cancel_right, hg] }

end Stand

end CFSG.ClassicalInvolution.Hat2A7S

namespace CFSG.ClassicalInvolution.Hat2A7S8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Hat2A7S

variable {G : Type} [Group G]

abbrev HypOmegaMod (Ω : Set (Subgroup G)) : Prop := HypOmegaGen Ω

abbrev PartIHyp (Ω : Set (Subgroup G)) : Prop := Hat2A7P1.PartIHypG8 Ω

alias l6_2 := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.l6_2

alias l6_7_proved := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.l6_7_proved

alias l6_11_proved := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.l6_11_proved

section Stand

variable [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}


structure AscStand (Ω : Set (Subgroup G)) (K : Subgroup G) : Prop where
  std : Std2A7 Ω K
  cls : Hat2A7P1.ClassicalClause8 Ω

theorem AscStand.hyp (h : AscStand Ω K) : HypOmegaGen Ω := h.std.hyp

theorem AscStand.mem (h : AscStand Ω K) : K ∈ Ω := h.std.mem

theorem AscStand.trans (h : AscStand Ω K) : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := h.std.trans

theorem AscStand.aEmpty (h : AscStand Ω K) : ∀ J ∈ Ω, AEmpty Ω J := h.std.aEmpty

theorem AscStand.of_mem (h : AscStand Ω K) (hJ : J ∈ Ω) : AscStand Ω J :=
  ⟨h.std.of_mem hJ, h.cls⟩

theorem AscStand.conj (h : AscStand Ω K) (n : G) : AscStand Ω (conjSub n K) :=
  ⟨h.std.conj n, h.cls⟩

structure Std8 (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  stand : AscStand Ω K
  noTwins : ∀ K' ∈ twinSet Ω K, K' = K
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hT : T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

@[expose] def C26_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → omegaNbrGen Ω K ≠ J ⊔ oddCoreOf (omegaNbrGen Ω K)

theorem Std8.of_std8A7 {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8A7 Ω K J S R T W z t) : Std8 Ω K J S R T W z t where
  stand := ⟨hs.stand, (partIHypG8_of_std2A7 hs.stand).cls⟩
  noTwins := hs.noTwins
  hz := hs.hz
  hJ := hs.hJ
  ht := hs.ht
  hR := hs.hR
  hT := hs.hT
  hW := hs.hW

theorem a7C26_1_of_c26_1 (h : C26_1) : A7C26_1 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  exact h G Ω K J S R T W z t (Std8.of_std8A7 hs) hdisc

end Stand

end CFSG.ClassicalInvolution.Hat2A7S8.Asc77
