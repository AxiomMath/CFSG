module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Sev2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section End

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

@[expose] def E178BenderQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z →
        IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G)) →
        IsSimpleGroup ↥(Subgroup.normalClosure ({z} : Set G)) →
        (∃ x ∈ Subgroup.normalClosure ({z} : Set G), ∃ y ∈ Subgroup.normalClosure ({z} : Set G),
          x * y ≠ y * x) →
        Subgroup.centralizer ((Subgroup.normalClosure ({z} : Set G) : Subgroup G) : Set G) = ⊥ →
        BenderSuzuki.IsBenderGroup ↥(Subgroup.normalClosure ({z} : Set G)) →
        BenderSuzuki.IsStronglyEmbeddedOrder (H.subgroupOf (Subgroup.normalClosure ({z} : Set G))) →
        False

@[expose] def E18_endQ8C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      (∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
        Subgroup.centralizer (F : Set G) = ⊥) →
      ∀ z : G, IsUniqueInvolution K z →
        IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
          (Subgroup.centralizer ({z} : Set G)) →
        FixesUniqueCoset z H →
        (∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) → h⁻¹ * z * h ≠ z →
          z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z → FixesUniqueCoset (z * (h⁻¹ * z * h)) H) →
        False

theorem e18_endQ8C_of (h : E178BenderQ8) : E18_endQ8C := by
  intro G _ _ Ω K S R W H c hF z hz hSyl h1 h2S
  obtain ⟨F, hFn, hFs, hFnab, hFc⟩ := hF
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h2 := CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_mul_of_isSylow2In hz2 hSyl h2S
  obtain ⟨hFeq, hB, hSE⟩ := CFSG.StronglyEmbedded.UniqueCoset.lemma_3_9 c.proper hz2 h1 h2 hFs hFnab
    hFc
  subst hFeq
  exact h G Ω K S R W H c z hz hSyl hFs hFnab hFc hB hSE

theorem minCexFalseQ8_of_steps_C (h6 : E18_6Q8) (h8 : E18_8zQ8) (h9 : E18_9Q8)
    (hend : E18_endQ8C) : MinCexFalseQ8 := by
  intro G _ _ Ω K S R W H c
  obtain ⟨K', ⟨-, z, hz1, -⟩, -⟩ := c.stand.twin
  obtain ⟨S', W', c', hSyl⟩ := c.exists_config_sylow_centralizer hz1
  obtain ⟨-, hF⟩ := h6 G Ω K S' R W' H c'
  have hzc : FixesUniqueCoset z H := h8 G Ω K S' R W' H c' z hz1
  exact hend G Ω K S' R W' H c' hF z hz1 hSyl hzc fun h h1 h2 h3 =>
    h9 G Ω K S' R W' H c' z hz1 h h1 h2 h3

end End

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
