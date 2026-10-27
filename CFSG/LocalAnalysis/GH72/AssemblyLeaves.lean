module

public import CFSG.LocalAnalysis.GH72.Assembly
public import CFSG.LocalAnalysis.GH72.AssemblySec7
public import CFSG.LocalAnalysis.GH72.Sec4Generation
public import CFSG.LocalAnalysis.GH72.Sec4Seventeen
public import CFSG.LocalAnalysis.GH72.Sec4Four
public import CFSG.LocalAnalysis.GH72.Sec4Prop46
public import CFSG.LocalAnalysis.GH72.Sec4Fourteen
public import CFSG.LocalAnalysis.GH72.Sec5Twenty
public import CFSG.LocalAnalysis.GH72.WalterE16
public import CFSG.LocalAnalysis.Mason73.L4SylowComparisonProof
public import CFSG.Milestones.CL_LIT_classical_involution_theorem

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups

theorem h417_of_leaves
    (h315 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
        (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
          H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
          bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
        (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
          K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
          bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
          (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁))) :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (H : Subgroup G), H.Normal →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H := by
  intro G _ _ 𝔖 H hH
  exact 𝔖.prop_4_17_of (fun hAS hA => 𝔖.lemma_4_7_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion)) H hH

theorem h66_of_leaves
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h315 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
        (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
          H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
          bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
        (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
          K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
          bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
          (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (h54 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A → ∀ {p : ℕ}, p.Prime → p ≠ 2 →
        (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
          ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
        ∃ H, 𝔖.IsCovering p A H) :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (s₁ s₂ : G),
      s₁ ∈ 𝔖.S₁ → s₂ ∈ 𝔖.S₂ → orderOf s₁ = 2 → orderOf s₂ = 2 → O (C s₁) ⊓ O (C s₂) = ⊥ := by
  intro G _ _ 𝔖
  have h315' := h315 𝔖.toSec3Setting 𝔖.fusion
  have h317' := h317 𝔖.toSec3Setting 𝔖.fusion
  have h315z := h315' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h317z := h317' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h44 := fun 𝔗 : Sec4Setting G =>
    𝔗.prop_4_4_of (h315 𝔗.toSec3Setting 𝔗.fusion) (h317 𝔗.toSec3Setting 𝔗.fusion) walterE16
  have h44J := fun 𝔗 : Sec4Setting G =>
    𝔗.prop_4_4_J_of (h315 𝔗.toSec3Setting 𝔗.fusion) (h317 𝔗.toSec3Setting 𝔗.fusion) walterE16
  have h47 := fun {A : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A) => 𝔖.lemma_4_7_of hAS hA h315'
  have h48 := fun {A : Subgroup G} (hAS : A ≤ 𝔖.S) (hA : IsE16 A) => 𝔖.lemma_4_8_of hAS hA h315'
  refine 𝔖.prop_6_6_of fun A hAS hA => ?_
  have h410 := 𝔖.lemma_4_10_of hAS hA h317z (h47 hAS hA) (h48 hAS hA)
  have h413 := 𝔖.lemma_4_13_of hA h315z (h47 hAS hA) (h48 hAS hA)
  have h414 := 𝔖.lemma_4_14_of hAS hA h410 h413 h44 h44J
  have h46 := 𝔖.prop_4_6_of (h44 𝔖) (h44J 𝔖) h315' h317' A hA
  exact 𝔖.prop_6_5_of hAS hA (h47 hAS hA) (h48 hAS hA) h410
    (𝔖.lemma_4_11_of hAS hA h315z isCyclic_of_odd_of_kleinFour_le_normalizer)
    (𝔖.lemma_4_12_of hAS hA (h47 hAS hA) (h48 hAS hA) fun _ 𝔗 => h32_37 𝔗) h413 h414
    (𝔖.lemma_4_15_of hAS hA h315z h317z isCyclic_of_odd_of_kleinFour_le_normalizer h47 h48)
    h46 (h54 𝔖 hAS hA)
    fun {p} hp hp2 => 𝔖.prop_5_20_of hAS hA hp hp2 (h54 𝔖 hAS hA hp hp2) (h46 p hp hp2) h410 h414

theorem h72_of_leaves
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h315 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
        (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
          H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
          bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
        (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
          K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
          bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
          (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (h54 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A → ∀ {p : ℕ}, p.Prime → p ≠ 2 →
        (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
          ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
        ∃ H, 𝔖.IsCovering p A H) :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∃ M₁, 𝔖.IsM1 A M₁) ∧ (¬ Group.IsSolvable (𝔖.N A) → ∃ N₁, 𝔖.IsN1 A N₁) := by
  refine h72_of ?_ ?_ ?_ ?_ ?_ (h417_of_leaves h315) (h66_of_leaves h32_37 h315 h317 h54)
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_7_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion)
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_8_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion)
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_9_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion)
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_11_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂)
      isCyclic_of_odd_of_kleinFour_le_normalizer
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_13_of hA (h315 𝔖.toSec3Setting 𝔖.fusion 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂)
      (𝔖.lemma_4_7_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion))
      (𝔖.lemma_4_8_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion))

theorem h73_of_leaves
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h315 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
        (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
          H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
          bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
        (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
          K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
          bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
          (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (h54 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A → ∀ {p : ℕ}, p.Prime → p ≠ 2 →
        (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
          ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
        ∃ H, 𝔖.IsCovering p A H) :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (¬ Group.IsSolvable (𝔖.N A) → ∀ N₁, 𝔖.IsN1 A N₁ → N₁.Normal) ∧
        (Group.IsSolvable (𝔖.N A) → ∀ M₁, 𝔖.IsM1 A M₁ → M₁.Normal) := by
  refine h73_of ?_ ?_ ?_ (h66_of_leaves h32_37 h315 h317 h54)
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_12_of hAS hA (𝔖.lemma_4_7_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion))
      (𝔖.lemma_4_8_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion)) fun _ 𝔗 => h32_37 𝔗
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_15_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂)
      (h317 𝔖.toSec3Setting 𝔖.fusion 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂)
      isCyclic_of_odd_of_kleinFour_le_normalizer
      (fun hAS' hA' => 𝔖.lemma_4_7_of hAS' hA' (h315 𝔖.toSec3Setting 𝔖.fusion))
      (fun hAS' hA' => 𝔖.lemma_4_8_of hAS' hA' (h315 𝔖.toSec3Setting 𝔖.fusion))
  · intro G _ _ 𝔖 A hAS hA
    exact 𝔖.lemma_4_16_of hAS hA (𝔖.lemma_4_7_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion))
      (𝔖.lemma_4_8_of hAS hA (h315 𝔖.toSec3Setting 𝔖.fusion))

section ClassicalInvolution

theorem hMason_of_leaves
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (h315 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
        (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
          H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
          bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
        (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
          K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
          bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
          (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (h317 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      HasProductFusion 𝔖.S₁ 𝔖.S₂ → ∀ (z₁ z₂ : G),
        (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
        (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) → HasNormalTwoComplement (C (z₁ * z₂)))
    (h54 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A → ∀ {p : ℕ}, p.Prime → p ≠ 2 →
        (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
          ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
        ∃ H, 𝔖.IsCovering p A H) :
    ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G,
        Nonempty (↥(P : Subgroup G) ≃* CFSG.CGT.Stroth77.L4Sylow.L4Model n) →
        CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G :=
  hMason_of_sections CFSG.Milestones.cl_lit_classical_involution_theorem_models
    CFSG.LocalAnalysis.Mason73.l4SylowComparison h32_37 (h417_of_leaves h315)
    (h72_of_leaves h32_37 h315 h317 h54) (h73_of_leaves h32_37 h315 h317 h54)

end ClassicalInvolution

end CFSG.GH72
