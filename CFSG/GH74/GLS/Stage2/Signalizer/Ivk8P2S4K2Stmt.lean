module

public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

@[expose] def IVK_8_13_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H J₁ J₂ : Subgroup G, H ≠ ⊤ → IsCompIn H J₁ → IsCompIn H J₂ → J₁ ≠ J₂ → orderOf z = 2 →
      z ∈ normalizer (J₁ : Set G) → z ∈ normalizer (J₂ : Set G) →
      ⁅J₁, zpowers z⁆ = J₁ → ⁅J₂, zpowers z⁆ = J₂ →
      ∀ x ∈ H, J₁.map (MulAut.conj x).toMonoidHom = J₂ → J₂.map (MulAut.conj x).toMonoidHom = J₁ →
        ∀ (p : ℕ) (P : Subgroup G), p.Prime → p ≠ 2 → IsPGroup p ↥P →
          P ≤ H ⊓ normalizer (J₁ : Set G) ⊓ normalizer (J₂ : Set G) → (∀ y ∈ P, z * y = y * z) →
          (∀ c ∈ H, c * z = z * c → c ∈ normalizer (P : Set G)) →
          ¬ P ≤ centralizer (J₁ : Set G) → ¬ P ≤ centralizer (J₂ : Set G) →
            ⁅x, z⁆ ∈ J₁ ⊔ J₂ ⊔ centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
