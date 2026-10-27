module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

attribute [instance] HatModelU.addCommGroup HatModelU.module HatModelU.finite

@[expose] def Lemma12_8_8_two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ D : HatModelU (u128 V V₁),
      (∀ v, D.B v v = 0) ∧ (∀ v, (∀ w, D.B v w = 0) → v = 0) ∧
      (∀ γ ∈ D.img (Subgroup.normalizer (V₁ : Set G)), ∀ v w, D.B (γ v) (γ w) = D.B v w) ∧
      (frattiniOf (zU128 V V₁) = ⊥ → ∃ q : D.V → ZMod 2,
        (∀ u ∈ u128 V V₁, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
        (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
        ∀ γ ∈ D.img (Subgroup.normalizer (V₁ : Set G)), ∀ v, q (γ v) = q v)

@[expose] def Lemma12_8_8_four_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → n ≤ 3 →
      L ≤ conjClosure (u128 V V₁) L ∧
        AlmostSpecialL3Hyp 1 V V₁ L T (Subgroup.normalizer (V₁ : Set G))

@[expose] def Lemma12_8_11_hat_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ a ∈ V₂, a ∉ V₁ → ∀ D : HatModelU (u128 V V₁),
      ((∀ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g), ∃ f : D.V →ₗ[ZMod 2] ZMod 2,
          f (D.π a) = 0 ∧
          ∀ w ∈ D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g), x w = w + f w • D.π a) ∧
        ∀ f : D.V →ₗ[ZMod 2] ZMod 2, f (D.π a) = 0 →
          ∃ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g),
            ∀ w ∈ D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g),
              x w = w + f w • D.π a) ∧
      Module.finrank (ZMod 2) ↥(D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g)) +
          Nat.log 2 ((D.img (CFSG.conjugate (zU128 V V₁) g)).relIndex
            (D.img (CFSG.conjugate (w128 V V₁ V₂) g))) =
        Module.finrank (ZMod 2) D.V - 1 ∧
      ((∃ v : D.V, (∀ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g), x v = v) ∧ v ≠ 0 ∧
          v ≠ D.π a) →
        ∃ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g), x ≠ 1 ∧
          Module.finrank (ZMod 2) ↥(LinearMap.range (x.toLinearMap - LinearMap.id)) ≤ 2 ∧
          D.π a ∈ LinearMap.range (x.toLinearMap - LinearMap.id))

@[expose] def Lemma12_8_12_hat_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ a ∈ V₂, a ∉ V₁ → ∀ D : HatModelU (u128 V V₁),
      G101Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
          (D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g))
          (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) (D.img (CFSG.conjugate (zU128 V V₁) g)) ∧
      G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
          (D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g))
          (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) (D.img (CFSG.conjugate (zU128 V V₁) g)) ∧
      G11.G112ConclusionFix D.B (D.img (Subgroup.normalizer (V₁ : Set G)))
        (D.img (CFSG.conjugate (w128 V V₁ V₂) g))

end CFSG.Quasithin.H13
