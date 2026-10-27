module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.Stage4.RestSetup
public import CFSG.GH74.GLS.Stage4.T2NumGtMixDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

@[expose] def Ch6MixSing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : T2N3 G) (u : G), Ch6Sec5M N u → N.q₂ < N.q₁ →
    (∀ k : ℕ, 2 ^ k ∣ N.q₁ + 1 ↔ 2 ^ k ∣ N.q₂ - 1) →
      ∃ y ∈ N.H ⊓ N.K₁, y ∉ Subgroup.zpowers N.z ∧ (orderOf y).Prime ∧ Odd (orderOf y) ∧
        orderOf y ∣ N.q₁ + 1 ∧ N.a * y * N.a⁻¹ = y

@[expose] def Ch6MixLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ → q₂ < q₁ → q₁ % 4 ≠ q₂ % 4 →
      ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
        Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
          ∀ (p n : ℕ), p.Prime → p ≠ 2 → q₂ = p ^ n →
            ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
              Ch6Coord2 N.toT2N2.toT2N1 → Ch6Sec5M N u →
                ∀ y ∈ N.H ⊓ N.K₁, y ∉ Subgroup.zpowers N.z → (orderOf y).Prime → Odd (orderOf y) →
                  orderOf y ∣ N.q₁ + 1 → N.a * y * N.a⁻¹ = y →
                    ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
                      (IsSLnEps 3 ↥J 1 q₂ ∨ IsLnEps 3 ↥J 1 q₂)

end CFSG.GH74.GLS.Stage4.Rest
