module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmgLayer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmgGold

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.Open
open scoped MatrixGroups

@[expose] def U3C1GmgIdentGoldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (w s : G) (P : Subgroup G),
    U3C1OuterSwapHigh G L f t T R₂ D d V U U₁ w s P → (∀ u ∈ U₁, s * u * s⁻¹ ∈ U₁) →
      (∃ S : Sylow 2 G, (S : Subgroup G) = swapS₂ P U T) →
      (∀ g : G, g * t * g⁻¹ ∈ swapS₂ P U T → g * t * g⁻¹ ∈ U ⊔ T) →
      (∀ g : G, g * t * g⁻¹ ≠ t * w) →
      IsSylowOf 2 (swapS₂ P U T ⊓ centralizer ({t * w} : Set G))
        (centralizer ({t * w} : Set G)) →
      ∀ J : Subgroup G, (U₁ ⊓ centralizer ({t * w} : Set G)) ⊔ zpowers (t * w) ≤ J →
        J ≤ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) →
        (∀ a ∈ J, ∀ b ∈ J, a * b = b * a) →
        (∀ a ∈ J, ∀ g ∈ centralizer ({t * w} : Set G),
          g⁻¹ * a * g ∈ swapS₂ P U T ⊓ centralizer ({t * w} : Set G) → g⁻¹ * a * g ∈ J) →
        ∀ M : Subgroup (centralizer ({t * w} : Set G)),
          Subgroup.normalClosure
            ((J.subgroupOf (centralizer ({t * w} : Set G)) :
              Subgroup (centralizer ({t * w} : Set G))) : Set (centralizer ({t * w} : Set G))) = M →
          CFSG.oddCore M = ⊥ →
        ∀ Q : Sylow 2 (centralizer ({t * w} : Set G)),
          (Q : Subgroup (centralizer ({t * w} : Set G))).map
            (centralizer ({t * w} : Set G)).subtype =
              swapS₂ P U T ⊓ centralizer ({t * w} : Set G) →
          CFSG.Open.pCore 2 M ⊔ goldschmidtLayer M = ⊤ →
          (J.subgroupOf (centralizer ({t * w} : Set G))).subgroupOf M = CFSG.Open.pCore 2 M ⊔
            Subgroup.closure {x | x ∈ (Q : Subgroup (centralizer ({t * w} : Set G))).subgroupOf M ⊓
              goldschmidtLayer M ∧ x ^ 2 = 1} →
          (∀ K : Subgroup M, IsComponentOf K ⊤ → goldschmidtSimpleType (K ⧸ Subgroup.center K)) →
        (∃ (K : Subgroup G) (p n : ℕ) (_ : Fact p.Prime),
            (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
            Nonempty (K ≃* PSL(2, GaloisField p n)) ∧
            K ≤ centralizer ({t * w} : Set G) ∧
            IsSylowOf 2 (U₁ ⊓ centralizer ({t * w} : Set G)) K ∧
            D ⊓ centralizer ({t * w} : Set G) ≤ K) ∨
        (∃ (K₁ E₁ : Subgroup G) (p n : ℕ) (_ : Fact p.Prime),
            (p = 2 ∧ 2 ≤ n ∨ p ≠ 2 ∧ (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5)) ∧
            Nonempty (K₁ ≃* PSL(2, GaloisField p n)) ∧
            K₁ ≤ centralizer ({t * w} : Set G) ∧
            (∀ a ∈ K₁, ∀ b ∈ K₁, a * (t * b * t⁻¹) = t * b * t⁻¹ * a) ∧
            IsSylowOf 2 (U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁) K₁ ∧
            (∀ x ∈ U₁ ⊓ centralizer ({t * w} : Set G),
              ∃ x₁ ∈ U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁,
                ∃ x₂ ∈ U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁, x = x₁ * (t * x₂ * t⁻¹)) ∧
            E₁ ≤ K₁ ∧
            E₁ ≤ normalizer ((U₁ ⊓ centralizer ({t * w} : Set G) ⊓ K₁ : Subgroup G) : Set G) ∧
            Odd (Nat.card E₁) ∧
            ∀ e ∈ D ⊓ centralizer ({t * w} : Set G),
              ∃ e₁ ∈ E₁, ∃ e₂ ∈ E₁, e = e₁ * (t * e₂ * t⁻¹))

theorem u3C1GmgIdentInput_of_gold
    (hTop : CFSG.Goldschmidt.TopStatement) (hI : U3C1GmgIdentGoldInput) : U3C1GmgIdentInput := by
  intro G _ _ L f t T R₂ D d V U U₁ w s P hW h1 h2 h3 h4 h5 J hJ1 hJ2 hJ3 hJ4
  obtain ⟨hO, Q, hQ, hg1, hg2, hg3⟩ := hW.gmg_goldschmidt hTop h5 hJ2 hJ3 hJ4 _ rfl
  exact hI G L f t T R₂ D d V U U₁ w s P hW h1 h2 h3 h4 h5 J hJ1 hJ2 hJ3 hJ4 _ rfl hO Q hQ hg1 hg2
    hg3

theorem u3C1GmsLayerInput_of_gold
    (hTop : CFSG.Goldschmidt.TopStatement) (hB : PSL2BorelInput) (hI : U3C1GmgIdentGoldInput) :
    U3C1GmsLayerInput :=
  u3C1GmsLayerInput_of_ident hB (u3C1GmgIdentInput_of_gold hTop hI)

end CFSG.SeitzReduction.RankOne
