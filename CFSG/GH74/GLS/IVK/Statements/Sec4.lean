module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GorensteinWalter
open scoped commutatorElement

section Local

variable {K : Type} [Group K]

@[expose] def Ez (z : K) : Subgroup K :=
  (layer ↥(centralizer ({z} : Set K))).map (centralizer ({z} : Set K)).subtype

@[expose] def O2z (z : K) : Subgroup K :=
  (oResidual 2 ↥(centralizer ({z} : Set K))).map (centralizer ({z} : Set K)).subtype

end Local

@[expose] def IVK_4_4a : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ε : ℤ) (p n : ℕ), p.Prime → p ≠ 2 →
    IsLnEps 3 K ε (p ^ n) → ∀ U : Subgroup K, IsFourSubgroup U → ∀ u ∈ U, ∀ u' ∈ U,
      orderOf u = 2 → orderOf u' = 2 → u ≠ u' →
        (3 < p ^ n → Subgroup.closure ((Ez u : Set K) ∪ (Ez u' : Set K)) = ⊤) ∧
        (p ^ n = 3 → Subgroup.closure ((O2z u : Set K) ∪ (O2z u' : Set K)) = ⊤)

@[expose] def IVK_4_4b : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ε : ℤ) (p n : ℕ), p.Prime → p ≠ 2 →
    IsLnEps 3 K ε (p ^ n) → ∀ S : Sylow 2 K,
      (¬ ((p ^ n : ℕ) : ℤ) ≡ ε [ZMOD 4] → ∃ m : ℕ, IsSemidihedralTwoGroup ↥S m) ∧
      (((p ^ n : ℕ) : ℤ) ≡ ε [ZMOD 4] → ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥S ≃* Open.WreathedTwoGroup m))

@[expose] def IVK_4_8a : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → 3 < Nat.card F →
    ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) [K.Normal]
      (e : ↥K ≃* StatedProj (StatedSp 2 F)) (Fh : Subgroup H), K ⊓ Fh = ⊥ → K ⊔ Fh = ⊤ →
      Odd (Nat.card ↥Fh) →
      (∀ x ∈ Fh, (MulAut.conjNormal x : MulAut ↥K) ∈ fieldAutSubOf (StatedSp 2 F)
        (fieldStable_statedSp 2) e) →
        2 * Nat.card H = Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) * Nat.card ↥Fh

@[expose] def IVK_4_8b : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → 3 < Nat.card F →
    ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) [K.Normal]
      (e : ↥K ≃* StatedProj (StatedSp 2 F)) (Fh : Subgroup H), K ⊓ Fh = ⊥ → K ⊔ Fh = ⊤ →
      Odd (Nat.card ↥Fh) →
      (∀ x ∈ Fh, (MulAut.conjNormal x : MulAut ↥K) ∈ fieldAutSubOf (StatedSp 2 F)
        (fieldStable_statedSp 2) e) →
      ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (Nat.card F : ℤ) ≡ ε [ZMOD 4] →
      ∀ d : ℕ, (d : ℤ) = Nat.card F - ε →
        ∃ z t : H, z ∈ K ∧ t ∈ K ∧ IsCentralInvolution z ∧ orderOf t = 2 ∧
          (∀ x : H, orderOf x = 2 → IsConj z x ∨ IsConj t x) ∧ ¬ IsConj z t ∧
          (∃ K₁ : Subgroup H, K₁ ≤ K ∧ HasSL2Model ↥K₁ (fun q => q = Nat.card F) ∧
            K₁ ⊓ K₁.map (MulAut.conj t).toMonoidHom = zpowers z ∧
            (∀ φ ∈ Fh, ∀ x ∈ K₁, φ * x * φ⁻¹ ∈ K₁) ∧
            centralizer ({z} : Set H) = K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ⊔ zpowers t ⊔ Fh) ∧
          (∃ (E J : Subgroup H) (y : H), E ≤ K ∧ J ≤ K ∧ orderOf y = 2 ∧
            (∀ a ∈ E, ∀ b ∈ J, a * b = b * a) ∧ E ⊓ J = ⊥ ∧
            IsDihedralOrder ↥E d ∧ IsL2 ↥J (fun q => q = Nat.card F) ∧
            IsDihedralOrder ↥(E ⊔ zpowers y) (2 * d) ∧
            IsPGL2 ↥(J ⊔ zpowers y) (fun q => q = Nat.card F) ∧
            (∀ φ ∈ Fh, ∀ x ∈ E, φ * x * φ⁻¹ ∈ E) ∧ (∀ φ ∈ Fh, ∀ x ∈ J, φ * x * φ⁻¹ ∈ J) ∧
            centralizer ({t} : Set H) = (E ⊔ J) ⊔ zpowers y ⊔ Fh)

@[expose] def IVK_4_10 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (q : ℕ), Odd q → 5 ≤ q → IsSp4L4U4 K q →
    ∀ (P : Sylow 2 K) (z : K), z ∈ (P : Subgroup K) → orderOf z = 2 →
      (∀ x ∈ (P : Subgroup K), x * z = z * x) →
        ∃ (t w : K) (E₁ E₂ : Subgroup K), t ∈ (P : Subgroup K) ∧ w ∈ (P : Subgroup K) ∧
          orderOf t = 2 ∧ (w = 1 ∨ orderOf w = 2) ∧ Commute t w ∧
          (P : Subgroup K) = ((P : Subgroup K) ⊓ Ez z) ⊔ zpowers t ⊔ zpowers w ∧
          Ez z ⊓ (zpowers t ⊔ zpowers w) = ⊥ ∧
          IsConj z t ∧ Ez z = E₁ ⊔ E₂ ∧ E₂ = E₁.map (MulAut.conj t).toMonoidHom ∧
          HasSL2Model ↥E₁ (fun r => r = q) ∧ E₁ ⊓ E₂ = zpowers z ∧
          (∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) ∧
          normalizer (E₁ : Set K) ⊓ (P : Subgroup K) = ((P : Subgroup K) ⊓ Ez z) ⊔ zpowers w ∧
          (w = 1 ↔ IsPSp4 K q) ∧
          (∀ x : K, orderOf x = 2 → IsConj z x ∨ IsConj (t * z) x) ∧ ¬ IsConj z (t * z) ∧
          (∀ x ∈ Ez z, orderOf x = 2 → x ≠ z → IsConj (t * z) x) ∧
          (w ≠ 1 → ∀ Ei ∈ ({E₁, E₂} : Set (Subgroup K)),
            ∃ _ : ((zpowers z).subgroupOf (Ei ⊔ zpowers w)).Normal,
              IsPGL2 (↥(Ei ⊔ zpowers w) ⧸ (zpowers z).subgroupOf (Ei ⊔ zpowers w))
                (fun r => r = q)) ∧
          (w ≠ 1 → IsConj z (t * w) ∧
            ∀ x ∈ (P : Subgroup K) ⊓ Ez z, orderOf (x * w) = 2 → IsConj z (x * w)) ∧
          ∀ y : K, IsCentralInvolution y → IsConj z y

@[expose] def IsG2Sp4L4U4 (K : Type) [Group K] (q : ℕ) : Prop :=
  (∃ p f : ℕ, p.Prime ∧ q = p ^ f ∧ LieModel K .G2 0 p f) ∨ IsPSp4 K q ∨ IsLnEps 4 K 1 q ∨
    IsLnEps 4 K (-1) q

end CFSG.GH74.GLS.IVK
