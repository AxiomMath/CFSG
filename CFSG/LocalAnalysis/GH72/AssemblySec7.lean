module

public import CFSG.LocalAnalysis.GH72.Sec7Prop72
public import CFSG.LocalAnalysis.GH72.Sec7Three
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups

theorem h72_of
    (h47 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
        CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
        𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
        𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
        (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
        (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
          (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
        CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
        𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
        𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
        (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
        (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
          (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h49 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∀ T₁ : Subgroup G, T₁ ≤ 𝔖.S₁ → T₁ ≠ ⊥ →
          ∀ K ∈ ({centralizer (T₁ : Set G), normalizer (T₁ : Set G)} : Set (Subgroup G)),
            let K₀ := (K ⊓ 𝔖.M₀ A) ⊔ O K
            K₀ ≤ K ∧ (K₀.subgroupOf K).Normal ∧ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ K₀ ∧
              QuotIso K₀ (O K) (𝔖.M₀ A) (O (𝔖.M A))) ∧
        (∀ T₂ : Subgroup G, T₂ ≤ 𝔖.S₂ → T₂ ≠ ⊥ →
          ∀ K ∈ ({centralizer (T₂ : Set G), normalizer (T₂ : Set G)} : Set (Subgroup G)),
            let K₀ := (K ⊓ 𝔖.N₀ A) ⊔ O K
            K₀ ≤ K ∧ (K₀.subgroupOf K).Normal ∧ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ K₀ ∧
              QuotIso K₀ (O K) (𝔖.N₀ A) (O (𝔖.N A))))
    (h411 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∀ x ∈ 𝔖.X A, x ≠ 1 → ∀ D : Subgroup G, D ≤ C x → Odd (Nat.card D) →
          A ≤ normalizer (D : Set G) → ⁅D, 𝔖.X A⁆ ⊔ ⁅⁅D, 𝔖.Y A⁆, ⁅D, 𝔖.Y A⁆⁆ ≤ O (C x)) ∧
        (∀ y ∈ 𝔖.Y A, y ≠ 1 → ∀ D : Subgroup G, D ≤ C y → Odd (Nat.card D) →
          A ≤ normalizer (D : Set G) → ⁅D, 𝔖.Y A⁆ ⊔ ⁅⁅D, 𝔖.X A⁆, ⁅D, 𝔖.X A⁆⁆ ≤ O (C y)))
    (h413 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        ∀ (H : Subgroup G), H ≠ ⊤ →
          (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H →
            O H ⊓ C x ≤ O (C x)) ∧
          (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H →
            O H ⊓ C y ≤ O (C y)))
    (h417 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (H : Subgroup G),
      H.Normal →
        ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ H ∧ ¬ CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ H)
    (h66 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (s₁ s₂ : G),
      s₁ ∈ 𝔖.S₁ → s₂ ∈ 𝔖.S₂ → orderOf s₁ = 2 → orderOf s₂ = 2 → O (C s₁) ⊓ O (C s₂) = ⊥) :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (∃ M₁, 𝔖.IsM1 A M₁) ∧ (¬ Group.IsSolvable (𝔖.N A) → ∃ N₁, 𝔖.IsN1 A N₁) := by
  intro G _ _ 𝔖 A hAS hA
  exact 𝔖.prop_7_2_of hAS hA (fun _ => h47 𝔖) (fun _ => h48 𝔖) (fun _ => h49 𝔖)
    (fun _ => h411 𝔖) (fun _ => h413 𝔖) (h417 𝔖) (h66 𝔖)

theorem h73_of
    (h412 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        ∀ (H : Subgroup G), H ≠ ⊤ → 𝔖.M A ≤ H → 𝔖.N A ≤ H →
          ∀ t ∈ H, orderOf t = 2 → ∃ h ∈ H, h * t * h⁻¹ ∈ A)
    (h415 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        ∀ (a : G), a ∈ A → a ≠ 1 →
          C a ≤ xySup (𝔖.X A) (𝔖.Y A) (fun x y => O (C a) ⊓ O (C x) ⊓ O (C y)) ⊔
            (C a ⊓ 𝔖.M₀ A) ⊔ (C a ⊓ 𝔖.N₀ A) ⊔ (C a ⊓ normalizer (A : Set G)))
    (h416 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        𝔖.M A = ⨆ (T₂ : Subgroup G) (_ : T₂ ≤ 𝔖.S₂) (_ : T₂ ≠ ⊥),
          𝔖.M A ⊓ normalizer (T₂ : Set G) ∧
        (¬ QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => Nonempty (L ≃* PSL(2, ZMod 5))) →
          𝔖.N A = ⨆ (T₁ : Subgroup G) (_ : T₁ ≤ 𝔖.S₁) (_ : T₁ ≠ ⊥),
            𝔖.N A ⊓ normalizer (T₁ : Set G)))
    (h66 : ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) (s₁ s₂ : G),
      s₁ ∈ 𝔖.S₁ → s₂ ∈ 𝔖.S₂ → orderOf s₁ = 2 → orderOf s₂ = 2 → O (C s₁) ⊓ O (C s₂) = ⊥) :
    ∀ {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G},
      A ≤ 𝔖.S → IsE16 A →
        (¬ Group.IsSolvable (𝔖.N A) → ∀ N₁, 𝔖.IsN1 A N₁ → N₁.Normal) ∧
        (Group.IsSolvable (𝔖.N A) → ∀ M₁, 𝔖.IsM1 A M₁ → M₁.Normal) := by
  intro G _ _ 𝔖 A hAS hA
  exact 𝔖.prop_7_3_of hAS hA (h412 𝔖 hAS hA) (h415 𝔖 hAS hA) (h416 𝔖 hAS hA) (h66 𝔖)

end CFSG.GH72
