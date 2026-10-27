module

public import CFSG.LocalAnalysis.GH72.AssemblyLeaves
public import CFSG.LocalAnalysis.GH72.Sec5E4bLeaves
public import CFSG.LocalAnalysis.GH72.Sec5Four
public import CFSG.LocalAnalysis.GH72.Sec5A
public import CFSG.LocalAnalysis.GH72.Sec5One
public import CFSG.LocalAnalysis.GH72.Sec5OneN
public import CFSG.LocalAnalysis.GH72.G3cSeventeen

public section

namespace CFSG.GH72

open Subgroup

theorem prop_5_4_closed :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A → ∀ {p : ℕ}, p.Prime → p ≠ 2 →
        (∃ D : Subgroup G, IsPGroup p D ∧ A ≤ normalizer (D : Set G) ∧
          ¬ A ≤ centralizer (D : Set G) ∧ XYGenerated (𝔖.X A) (𝔖.Y A) D) →
        ∃ H, 𝔖.IsCovering p A H := by
  intro G _ _ 𝔖 A hAS hA p hp hp2 hD
  have h315' := Sec3Setting.prop_3_15 𝔖.toSec3Setting 𝔖.fusion
  have h317' := Sec3Setting.prop_3_17 𝔖.toSec3Setting 𝔖.fusion
  have h315z := h315' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h317z := h317' 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have h44 := 𝔖.prop_4_4_of h315' h317' walterE16
  have h47 := 𝔖.lemma_4_7_of hAS hA h315'
  have h48 := 𝔖.lemma_4_8_of hAS hA h315'
  have h51 := 𝔖.lemma_5_1_of hAS hA hp hp2
    (Sec4Setting.sec5_one_M_of h44 h315z h317z h47 h48 hAS hA)
    (Sec4Setting.sec5_one_N_of hAS hA h44 h315z h317z h47 h48) h47 h48
  exact 𝔖.prop_5_4_of hAS hA hp h51
    (hmain_of_leaves Sec3Setting.prop_3_15 Sec3Setting.prop_3_17 hp hp2)
    (hE4b_of_leaves Sec3Setting.prop_3_15 Sec3Setting.prop_3_17 𝔖 hAS hA hp hp2) hD

section ClassicalInvolution

theorem hMason_of_exists_productFusion
    (h32_37 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G),
      ∃ S₁' S₂' : Subgroup G, DDDecomp (𝔖.S : Subgroup G) S₁' S₂' ∧ HasProductFusion S₁' S₂') :
    ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      ∀ {n : ℕ}, 3 ≤ n → ∀ P : Sylow 2 G,
        Nonempty (↥(P : Subgroup G) ≃* CFSG.CGT.Stroth77.L4Sylow.L4Model n) →
        CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G :=
  hMason_of_leaves h32_37 Sec3Setting.prop_3_15 Sec3Setting.prop_3_17 prop_5_4_closed

end ClassicalInvolution

end CFSG.GH72
