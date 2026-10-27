module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS CFSG.GorensteinWalter
open scoped commutatorElement

structure ProdSL2 (H : Type) [Group H] (K₁ K₂ : Subgroup H) (F₁ F₂ : Type) [Field F₁] [Field F₂] :
    Prop where
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  iso₁ : Nonempty (↥K₁ ≃* SL2 F₁)
  iso₂ : Nonempty (↥K₂ ≃* SL2 F₂)
  card_inter : Nat.card ↥(K₁ ⊓ K₂) = 2
  fstar_normal : (K₁ ⊔ K₂).Normal
  fstar_centralizer : centralizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) ≤ K₁ ⊔ K₂

@[expose] def IsDiagInv {H : Type} [Group H] (K₁ K₂ : Subgroup H) (F₁ F₂ : Type) [Field F₁]
    [Field F₂] (w : H) : Prop :=
  (∀ x ∈ K₁, w * x * w⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, w * x * w⁻¹ ∈ K₂) ∧
  (∃ _ : (K₁.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)).Normal,
    Nonempty ((↥(K₁ ⊔ K₂ ⊔ zpowers w)) ⧸ (K₁.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)) ≃* PGL2 F₂)) ∧
  (∃ _ : (K₂.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)).Normal,
    Nonempty ((↥(K₁ ⊔ K₂ ⊔ zpowers w)) ⧸ (K₂.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers w)) ≃* PGL2 F₁))

@[expose] def IVK_3_1a : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ z ∈ K₁ ⊓ K₂, z ≠ 1 →
      ∀ x y : H, x ∈ K₁ ⊔ K₂ → y ∈ K₁ ⊔ K₂ → orderOf x = 2 → orderOf y = 2 → x ≠ z → y ≠ z →
        ConjUnder (K₁ ⊔ K₂) x y

@[expose] def IVK_3_1b : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ z ∈ K₁ ⊓ K₂, z ≠ 1 → ∀ T : Sylow 2 H, ∀ t ∈ (T : Subgroup H),
      orderOf t = 2 → K₁.map (MulAut.conj t).toMonoidHom = K₂ →
        (∀ x : H, (∃ p ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂), x = p * t) → orderOf x = 2 →
          ConjUnder (K₁ ⊔ K₂) x t ∨ ConjUnder (K₁ ⊔ K₂) x (z * t)) ∧
        Nonempty (↥(centralizer ({t} : Set H) ⊓ (K₁ ⊔ K₂)) ≃* L2 F₁ × Multiplicative (ZMod 2))

@[expose] def IVK_3_1c : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ T : Sylow 2 H, ∀ w ∈ (T : Subgroup H), orderOf w = 2 →
      IsDiagInv K₁ K₂ F₁ F₂ w →
        (∀ x y : H, (∃ k ∈ K₁ ⊔ K₂, x = k * w) → (∃ k ∈ K₁ ⊔ K₂, y = k * w) →
          orderOf x = 2 → orderOf y = 2 → ConjUnder (K₁ ⊔ K₂) x y) ∧
        ∀ S : Sylow 2 ↥(centralizer ({w} : Set H) ⊓ (K₁ ⊔ K₂)), Nat.card ↥S = 4

@[expose] def IVK_3_1d : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ w : H, orderOf w = 2 → IsDiagInv K₁ K₂ F₁ F₂ w →
      oPrimeResidual 2 H = K₁ ⊔ K₂ ⊔ zpowers w → pRank 2 H = 3

@[expose] def IVK_3_1e : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ w t : H, orderOf w = 2 → IsDiagInv K₁ K₂ F₁ F₂ w →
      K₁.map (MulAut.conj t).toMonoidHom = K₂ →
      oPrimeResidual 2 H = K₁ ⊔ K₂ ⊔ zpowers w ⊔ zpowers t → pRank 2 H ≤ 4

@[expose] def IVK_3_1g : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ →
      (normalizer (K₁ : Set H)).index ≤ 2 ∧
      ∀ a ∈ normalizer (K₁ : Set H), ∀ b ∈ normalizer (K₁ : Set H), ⁅a, b⁆ ∈ K₁ ⊔ K₂

@[expose] def IVK_3_1h : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁] (H : Type) [Group H] [Finite H]
    (K₁ K₂ : Subgroup H), ProdSL2 H K₁ K₂ F₁ F₂ → L2Field F₁ →
      ∀ w : H, orderOf w = 2 → IsDiagInv K₁ K₂ F₁ F₂ w → K₁ ⊔ K₂ ⊔ zpowers w = ⊤ →
        ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ∀ x ∈ K₁,
          (Nat.card ↥(centralizer ({x} : Set H) ⊓ K₁) : ℤ) = Nat.card F₁ - ε →
          ∀ S : Sylow 2 ↥(centralizer ({x} : Set H)),
            (¬ (Nat.card F₁ : ℤ) ≡ ε [ZMOD 4] → ∃ n : ℕ, IsSemidihedralTwoGroup ↥S n) ∧
            ((Nat.card F₁ : ℤ) ≡ ε [ZMOD 4] → ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥S ≃* Open.WreathedTwoGroup n))

@[expose] def IVK_3_1i : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] (H : Type) [Group H] [Finite H] (K₁ K₂ : Subgroup H),
    ProdSL2 H K₁ K₂ F₁ F₂ → ∀ z ∈ K₁ ⊓ K₂, z ≠ 1 → ∀ T : Sylow 2 H,
      ∀ u ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂), orderOf u = 2 → u ≠ z →
        (∀ x ∈ (T : Subgroup H) ⊓ (K₁ ⊔ K₂), ∀ v ∈ zpowers u ⊔ zpowers z, x * v * x⁻¹ ∈ zpowers u ⊔ zpowers z) →
        ∀ t ∈ (T : Subgroup H), orderOf t = 2 → K₁.map (MulAut.conj t).toMonoidHom = K₂ →
        ∀ n : ℕ, Nat.card ↥((T : Subgroup H) ⊓ K₁) * 2 = 2 ^ (n + 1) →
          ∃ B₁ B₂ : Subgroup H, ∃ y : H, orderOf y = 2 ∧
            centralizer ({u} : Set H) ⊓ (((T : Subgroup H) ⊓ (K₁ ⊔ K₂)) ⊔ zpowers t) =
              (B₁ ⊔ B₂) ⊔ zpowers y ∧
            (∀ a ∈ B₁, ∀ b ∈ B₂, a * b = b * a) ∧ B₁ ⊓ B₂ = ⊥ ∧
            IsDihedralOrder ↥B₁ (2 ^ (n - 1)) ∧ IsDihedralOrder ↥B₂ (2 ^ (n - 1)) ∧
            IsDihedralOrder ↥(B₁ ⊔ zpowers y) (2 ^ n) ∧ IsDihedralOrder ↥(B₂ ⊔ zpowers y) (2 ^ n)

@[expose] def IVK_3_4a : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁] (H : Type) [Group H] [Finite H]
    (K₁ K₂ : Subgroup H), ProdSL2 H K₁ K₂ F₁ F₂ → L2Field F₁ → ∀ t : H, orderOf t = 2 →
      K₁.map (MulAut.conj t).toMonoidHom = K₂ → ∀ p n : ℕ, p.Prime → Nat.card F₁ = p ^ n →
        ∀ X D : Subgroup H, X ≤ K₁ ⊔ K₂ → IsPGroup p ↥X → Nat.card ↥X = p ^ (2 * n) →
          (∀ x ∈ X, t * x * t⁻¹ ∈ X) →
          X ⊔ D = normalizer (X : Set H) ⊓ (K₁ ⊔ K₂ ⊔ zpowers t) → X ⊓ D = ⊥ →
            Nat.card {W : Sylow p ↥(K₁ ⊔ K₂) // D ≤ (normalizer ((W : Subgroup ↥(K₁ ⊔ K₂)).map
              (K₁ ⊔ K₂).subtype : Set H))} = 4 ∧
            ∀ W₁ W₂ : Sylow p ↥(K₁ ⊔ K₂),
              D ≤ normalizer ((W₁ : Subgroup ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype : Set H) →
              D ≤ normalizer ((W₂ : Subgroup ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype : Set H) →
                ∃ g ∈ normalizer (D : Set H) ⊓ (K₁ ⊔ K₂),
                  (W₁ : Subgroup ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype =
                    ((W₂ : Subgroup ↥(K₁ ⊔ K₂)).map (K₁ ⊔ K₂).subtype).map (MulAut.conj g).toMonoidHom

@[expose] def IVK_3_4b : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁] (H : Type) [Group H] [Finite H]
    (K₁ K₂ : Subgroup H), ProdSL2 H K₁ K₂ F₁ F₂ → L2Field F₁ → ∀ t : H, orderOf t = 2 →
      K₁.map (MulAut.conj t).toMonoidHom = K₂ → ∀ p n : ℕ, p.Prime → Nat.card F₁ = p ^ n →
        Nat.card F₁ % 4 = 1 → ∀ X : Subgroup H, X ≤ K₁ ⊔ K₂ → IsPGroup p ↥X →
          Nat.card ↥X = p ^ (2 * n) → (∀ x ∈ X, t * x * t⁻¹ ∈ X) →
            ∃ g ∈ K₁ ⊔ K₂, (centralizer ({t} : Set H) ⊓ X).map (MulAut.conj g).toMonoidHom =
              ⁅X, zpowers t⁆

@[expose] def IVK_3_4c : Prop :=
  ∀ (F₁ F₂ : Type) [Field F₁] [Field F₂] [Finite F₁] (H : Type) [Group H] [Finite H]
    (K₁ K₂ : Subgroup H), ProdSL2 H K₁ K₂ F₁ F₂ → L2Field F₁ → ∀ t : H, orderOf t = 2 →
      K₁.map (MulAut.conj t).toMonoidHom = K₂ → ∀ p n : ℕ, p.Prime → Nat.card F₁ = p ^ n →
        Nat.card F₁ % 4 = 3 → oPrimeResidual 2 H = K₁ ⊔ K₂ ⊔ zpowers t →
          ∀ X : Subgroup H, X ≤ K₁ ⊔ K₂ → IsPGroup p ↥X → Nat.card ↥X = p ^ (2 * n) →
            (∀ x ∈ X, t * x * t⁻¹ ∈ X) → ∀ z ∈ K₁ ⊓ K₂, z ≠ 1 →
              centralizer ((⁅X, zpowers t⁆ : Subgroup H) : Set H) = X ⊔ zpowers z ∧ X ⊓ zpowers z = ⊥

end CFSG.GH74.GLS.IVK
