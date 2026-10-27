module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Lemmas
public import CFSG.GH74.GLS.C3.Layer1.Th2T1Rel

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_thm1_L37_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Cfg3 x y K T V W f z → IsSpecial x y K T f → V ≠ W →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
      (thompsonJ2 T = (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x) ∧ (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) = ⊥) ∧
      zCenter (thompsonJ2 T) = zpowers z ⊔ zpowers f ⊔ zpowers x ∧
      ∀ P₀ : Subgroup G, IsDihedralMaxIn P₀ (T ⊓ K) → T ⊓ centralizer ({f} : Set G) = T ⊓ normalizer (P₀ : Set G)

@[expose] def B_thm1_L38_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Cfg3 x y K T V W f z → V ≠ W →
      ∀ (S : Subgroup G) (a : G), IsSylowOf 2 S ⊤ → T ≤ S → a ∈ S → a ∈ normalizer (T : Set G) → a ∉ T → a ^ 2 ∈ T →
        ¬ HasL2Model (kBar K) (fun q => q = 5) →
        (zCenter T = zpowers x ⊔ zpowers z ∧
          Nat.card ↥T = 2 * Nat.card ↥(T ⊓ centralizer ((zCenter (thompsonJ2 T) : Subgroup G) : Set G))) ∧
        (T ⊓ K = closure {u : G | u ∈ thompsonJ2 T ∧ IsConj z u} ∧
          ∀ P₀ : Subgroup G, IsDihedralMaxIn P₀ (T ⊓ K) → ¬ ∀ t ∈ T, ∀ p ∈ P₀, t * p * t⁻¹ ∈ P₀) ∧
        (S ⊓ normalizer (T : Set G) = T ⊔ zpowers a ∧ a * x * a⁻¹ = x * z)

@[expose] def B_thm1_L39_third_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V₁ W₁ : Subgroup G) (f₁ z : G), Cfg3 x y K T V₁ W₁ f₁ z →
      layerI K f₁ ⊔ pPrimeCoreOf 2 (pumpJ K f₁) < pumpJ K f₁ →
      ∀ w₁ : G, Is2TerminalU2Triple f₁ w₁ (pumpJ K f₁) →
        Nat.card (kBar (pumpJ K f₁)) = Nat.card (kBar K) →
        ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
        ¬ HasL2Model (kBar K) (fun q => q = 5) →
        ∃ x₃ : G, IsConj x x₃ ∧ IsFMember f₁ (pumpJ K f₁) V₁ x₃

end CFSG.GH74.GLS
