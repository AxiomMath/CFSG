module

public import CFSG.GH74.QTGen4.Recog.G23.Abstract
public import CFSG.GH74.QTGen4.Recog.G23.Words

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {G : Type} [Group G]

@[expose] def SatWords {X : Type*} [Group X] {m : ℕ} (ws : List (List (Fin m × Bool)))
    (ρ : Fin m → X) : Prop :=
  ∀ r ∈ ws, FreeGroup.lift ρ (FreeGroup.mk r) = 1

structure HLetters (H H₁ H₂ : Subgroup G) (e : Fin 6 → G) : Prop where
  rels : SatisfiesWords g23WordsH e
  gen : Subgroup.closure (Set.range fun i : Fin 5 => e i.castSucc) = H
  gen₁ : Subgroup.closure ({e 0, e 1} : Set G) = H₁
  gen₂ : Subgroup.closure ({e 2, e 3} : Set G) = H₂

@[expose] def zOf (e : Fin 6 → G) : G := (e 0 * e 1) ^ 2

@[expose] def Psub (e : Fin 6 → G) : Subgroup G := Subgroup.closure {e 0, e 2}

@[expose] def Esub (e : Fin 6 → G) : Subgroup G := Subgroup.closure {e 4, zOf e}

structure Setup (G : Type) [Group G] (T H H₁ H₂ M : Subgroup G) (e : Fin 6 → G) : Prop where
  ctx : G23Ctx G T H H₁ H₂ M
  lets : HLetters H H₁ H₂ e

structure IsCentComplement (C L N : Subgroup G) : Prop where
  left_le : N ≤ C
  right_le : L ≤ C
  conj_mem : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N
  odd_card : Odd (Nat.card N)
  disjoint : N ⊓ L = ⊥
  sup_eq : N ⊔ L = C


structure HFacts (H H₁ H₂ : Subgroup G) (e : Fin 6 → G) : Prop where
  card_H : Nat.card H = 576
  card_P : Nat.card (Psub e) = 9
  elem_P : IsElemAbelian 3 (Psub e)
  cent₁ : Subgroup.centralizer {e 0} ⊓ H = Subgroup.zpowers (e 0) ⊔ H₂
  disj₁ : Subgroup.zpowers (e 0) ⊓ H₂ = ⊥
  cent₂ : Subgroup.centralizer {e 2} ⊓ H = Subgroup.zpowers (e 2) ⊔ H₁
  disj₂ : Subgroup.zpowers (e 2) ⊓ H₁ = ⊥
  norm₁ : Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) ⊓ H =
    (Subgroup.zpowers (e 0) ⊔ H₂) ⊔ Subgroup.zpowers (e 4)
  norm₂ : Subgroup.normalizer (Subgroup.zpowers (e 2) : Set G) ⊓ H =
    (Subgroup.zpowers (e 2) ⊔ H₁) ⊔ Subgroup.zpowers (e 4)
  centP : Subgroup.centralizer (Psub e : Set G) ⊓ H = Psub e ⊔ Subgroup.zpowers (zOf e)
  normP : Subgroup.normalizer (Psub e : Set G) ⊓ H = Psub e ⊔ Esub e
  centYp : Subgroup.centralizer {e 0 * e 2} ⊓ H = Psub e ⊔ Subgroup.zpowers (zOf e)
  normYp : Subgroup.normalizer (Subgroup.zpowers (e 0 * e 2) : Set G) ⊓ H = Psub e ⊔ Esub e
  centYm : Subgroup.centralizer {e 0 * (e 2)⁻¹} ⊓ H = Psub e ⊔ Subgroup.zpowers (zOf e)
  normYm : Subgroup.normalizer (Subgroup.zpowers (e 0 * (e 2)⁻¹) : Set G) ⊓ H =
    Psub e ⊔ Esub e
  invert₁ : ∀ c ∈ Subgroup.centralizer {e 0} ⊓ H, c * e 2 * c⁻¹ ≠ (e 2)⁻¹
  invert₂ : ∀ c ∈ Subgroup.centralizer {e 2} ⊓ H, c * e 0 * c⁻¹ ≠ (e 0)⁻¹
  conj_t₂ : ∃ g ∈ H₂ ⊔ Subgroup.zpowers (e 4), g * e 4 * g⁻¹ = e 4 * zOf e
  conj_t₁ : ∃ g ∈ H₁ ⊔ Subgroup.zpowers (e 4), g * e 4 * g⁻¹ = e 4 * zOf e
  centL₁ : Subgroup.centralizer {e 0} ⊓ H₁ = Subgroup.zpowers (e 0) ⊔ Subgroup.zpowers (zOf e)
  centL₂ : Subgroup.centralizer {e 2} ⊓ H₂ = Subgroup.zpowers (e 2) ⊔ Subgroup.zpowers (zOf e)
  invK : ∀ u ∈ H₁ ⊔ H₂, orderOf u = 2 → u ≠ zOf e → ∀ u' ∈ H₁ ⊔ H₂, orderOf u' = 2 →
    u' ≠ zOf e → ∃ h ∈ H, h * u * h⁻¹ = u'
  card_cent_t : Nat.card ↥(Subgroup.centralizer {e 4} ⊓ H) = 8
  odd_sub : ∀ S : Subgroup G, S ≤ H → Odd (Nat.card S) → Nat.card S ∣ 9 ∧
    (Nat.card S = 9 → ∃ h ∈ H, ∀ x ∈ Psub e, h * x * h⁻¹ ∈ S)
  order3 : ∀ x ∈ H, x ^ 3 = 1 → x ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ ∈ Psub e

@[expose] def OneClass (e : Fin 6 → G) : Prop :=
  ∀ u : G, orderOf u = 2 → IsConj (zOf e) u

structure VertexCore (e : Fin 6 → G) (H : Subgroup G) (σ : G) (L M : Subgroup G) : Prop where
  compl : IsCentComplement (Subgroup.centralizer {σ}) L M
  three : IsPGroup 3 M
  inf_H : M ⊓ H = Subgroup.zpowers σ
  conj_t : ∀ m ∈ M, e 4 * m * (e 4)⁻¹ ∈ M
  normalizer_eq : Subgroup.normalizer (Subgroup.zpowers σ : Set G) =
    Subgroup.centralizer {σ} ⊔ Subgroup.zpowers (e 4)
  card_cent : Nat.card ↥(M ⊓ Subgroup.centralizer {e 4}) = 1 ∨
    Nat.card ↥(M ⊓ Subgroup.centralizer {e 4}) = 3 ∨ Nat.card ↥(M ⊓ Subgroup.centralizer {e 4}) = 9
  card_cent' : Nat.card ↥(M ⊓ Subgroup.centralizer {e 4 * zOf e}) =
    Nat.card ↥(M ⊓ Subgroup.centralizer {e 4})
  card_eq : Nat.card M = 3 * Nat.card ↥(M ⊓ Subgroup.centralizer {e 4}) ^ 2
  sylow2 : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Subgroup.centralizer {σ} → Nat.card R ≤ 8

structure PbarCore (e : Fin 6 → G) (Pb : Subgroup G) : Prop where
  compl : IsCentComplement (Subgroup.centralizer (Psub e : Set G)) (Subgroup.zpowers (zOf e)) Pb
  three : IsPGroup 3 Pb
  P_le : Psub e ≤ Pb
  inf_cent_z : Pb ⊓ Subgroup.centralizer {zOf e} = Psub e
  conj_t : ∀ m ∈ Pb, e 4 * m * (e 4)⁻¹ ∈ Pb
  normalizer_eq : Subgroup.normalizer (Psub e : Set G) = Pb ⊔ Esub e

structure MixedCore (e : Fin 6 → G) (y : G) (N : Subgroup G) : Prop where
  compl : IsCentComplement (Subgroup.centralizer {y}) (Subgroup.zpowers (zOf e)) N
  three : IsPGroup 3 N
  P_le : Psub e ≤ N
  card_le : Nat.card N ≤ 3 ^ 6
  normalizer_eq : Subgroup.normalizer (Subgroup.zpowers y : Set G) = N ⊔ Esub e
  sylow2 : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Subgroup.centralizer {y} → Nat.card R ≤ 2

structure FourClasses (e : Fin 6 → G) : Prop where
  s12 : ¬ IsConj (e 0) (e 2)
  mixed : ¬ IsConj (e 0 * e 2) (e 0 * (e 2)⁻¹)
  pure_mixed : ∀ y ∈ ({e 0 * e 2, e 0 * (e 2)⁻¹} : Set G), ¬ IsConj (e 0) y ∧ ¬ IsConj (e 2) y

structure Cor37 (e : Fin 6 → G) (M₁ M₂ Pb : Subgroup G) : Prop where
  card_eq : Nat.card M₁ = Nat.card M₂
  cases : (Nat.card M₁ = 3 ∧ Nat.card Pb = 9) ∨ (Nat.card M₁ = 27 ∧ Nat.card Pb = 27) ∨
    (Nat.card M₁ = 243 ∧ Nat.card Pb = 81)
  card_Pb₁ : Nat.card Pb = 3 * Nat.card ↥(M₂ ⊓ Subgroup.centralizer {e 0})
  card_Pb₂ : Nat.card Pb = 3 * Nat.card ↥(M₁ ⊓ Subgroup.centralizer {e 2})
  Pb_eq₁ : Pb = (M₂ ⊓ Subgroup.centralizer {e 0}) ⊔ Subgroup.zpowers (e 0)
  Pb_eq₂ : Pb = (M₁ ⊓ Subgroup.centralizer {e 2}) ⊔ Subgroup.zpowers (e 2)

structure Local3 (e : Fin 6 → G) (H H₁ H₂ : Subgroup G) (M₁ M₂ Pb Np Nm : Subgroup G) :
    Prop where
  v₁ : VertexCore e H (e 0) H₂ M₁
  v₂ : VertexCore e H (e 2) H₁ M₂
  pb : PbarCore e Pb
  np : MixedCore e (e 0 * e 2) Np
  nm : MixedCore e (e 0 * (e 2)⁻¹) Nm
  four : FourClasses e
  cor : Cor37 e M₁ M₂ Pb


@[expose] def specialD (z : G) (H : Subgroup G) : Set G :=
  {x | x ∈ H ∧ ((x ^ 3 = 1 ∧ x ≠ 1) ∨ ∃ k : ℕ, 0 < k ∧ orderOf x = 2 * k ∧ x ^ k = z)}

structure SpecialSet (e : Fin 6 → G) (H : Subgroup G) : Prop where
  cent_le : ∀ x ∈ specialD (zOf e) H, Subgroup.centralizer {x} ≤ H
  fusion : ∀ x ∈ specialD (zOf e) H, ∀ y ∈ specialD (zOf e) H, IsConj x y →
    ∃ h ∈ H, h * x * h⁻¹ = y
  invert : ∀ x ∈ specialD (zOf e) H, ∀ u : G, u * u = 1 → u * x * u⁻¹ = x⁻¹ → u ∈ H
  central : ∀ h ∈ H, h * zOf e * h⁻¹ = zOf e

@[expose] def StepAArith (g : ℕ) (x₁ x₂ : ℤ) : Prop :=
  1 + x₁ + x₂ = 0 ∧ x₂ ≡ -153 [ZMOD 576] ∧ x₁.natAbs ∣ g ∧ x₂.natAbs ∣ g ∧
    (g : ℤ) * (x₁ * x₂ + 64 * x₂ + 81 * x₁) = 576 * 7200 * (x₁ * x₂)

structure B27State (e : Fin 6 → G) (M₁ Pb W₁ Mf : Subgroup G) (t' : G) : Prop where
  t'_mem : t' = e 4 ∨ t' = e 4 * zOf e
  card_W₁ : Nat.card W₁ = 3
  W₁_le : W₁ ≤ M₁ ⊓ Subgroup.centralizer {e 2}
  W₁_inv : ∀ w ∈ W₁, zOf e * w * (zOf e)⁻¹ = w⁻¹
  W₁_cent : ∀ w ∈ W₁, t' * w * t'⁻¹ = w
  Pb_eq : Pb = Psub e ⊔ W₁
  cent_Pb : Subgroup.centralizer (Pb : Set G) = Pb
  compl : IsCentComplement (Subgroup.normalizer (Pb : Set G)) (Esub e) Mf
  three : IsPGroup 3 Mf
  card_Mf : Nat.card Mf = 243
  M₁_normal : ∀ g ∈ Mf, ∀ m ∈ M₁, g * m * g⁻¹ ∈ M₁
  M₁_le : M₁ ≤ Mf
  s₂_mem : e 2 ∈ Mf
  inf_norm : Mf ⊓ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) =
    M₁ ⊔ Subgroup.zpowers (e 2)
  not_le_norm : ¬ Subgroup.normalizer (Pb : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G)
  cent_t' : Mf ⊓ Subgroup.centralizer {t'} = W₁
  derived : ⁅Mf, Mf⁆ = W₁
  card_cent_t'z : Nat.card ↥(Mf ⊓ Subgroup.centralizer {t' * zOf e}) = 9

structure MStruct (e : Fin 6 → G) (M₁ M₂ : Subgroup G) : Prop where
  card₁ : Nat.card M₁ = 243
  card₂ : Nat.card M₂ = 243
  exp₁ : ∀ m ∈ M₁, m ^ 3 = 1
  exp₂ : ∀ m ∈ M₂, m ^ 3 = 1
  comm₁ : ∀ x ∈ M₁, ∀ y ∈ M₁, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (e 0)
  comm₂ : ∀ x ∈ M₂, ∀ y ∈ M₂, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (e 2)
  nonab₁ : ∃ x ∈ M₁, ∃ y ∈ M₁, x * y ≠ y * x
  nonab₂ : ∃ x ∈ M₂, ∃ y ∈ M₂, x * y ≠ y * x
  card_Z₁ : Nat.card ↥(M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) = 27
  card_Z₂ : Nat.card ↥(M₂ ⊓ Subgroup.centralizer (M₂ : Set G)) = 27
  zinv₁ : ∀ m ∈ M₁, zOf e * m * (zOf e)⁻¹ * m ∈ Subgroup.zpowers (e 0)
  zinv₂ : ∀ m ∈ M₂, zOf e * m * (zOf e)⁻¹ * m ∈ Subgroup.zpowers (e 2)

structure Loc5 (e : Fin 6 → G) (M₁ M₂ Pb W : Subgroup G) : Prop where
  mstruct : MStruct e M₁ M₂
  card_Pb : Nat.card Pb = 81
  W_le₁ : W ≤ M₁ ⊓ Subgroup.centralizer {e 2}
  W_le₂ : W ≤ M₂ ⊓ Subgroup.centralizer {e 0}
  card_W : Nat.card W = 9
  W_inv : ∀ w ∈ W, zOf e * w * (zOf e)⁻¹ = w⁻¹
  W_eq₁ : ∀ x ∈ M₁ ⊓ Subgroup.centralizer {e 2}, zOf e * x * (zOf e)⁻¹ = x⁻¹ → x ∈ W
  W_eq₂ : ∀ x ∈ M₂ ⊓ Subgroup.centralizer {e 0}, zOf e * x * (zOf e)⁻¹ = x⁻¹ → x ∈ W
  card_ℓ₁ : Nat.card ↥(W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G))) = 3
  card_ℓ₂ : Nat.card ↥(W ⊓ (M₂ ⊓ Subgroup.centralizer (M₂ : Set G))) = 3
  ℓ_ne : W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) ≠
    W ⊓ (M₂ ⊓ Subgroup.centralizer (M₂ : Set G))

structure VertexHyp (σ a b z : G) (M W : Subgroup G) (w₁ w₂ : G) : Prop where
  a3 : a ^ 3 = 1
  b3 : b ^ 3 = 1
  rel : b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a = 1
  z_def : z = (a * b) ^ 2
  card_L : Nat.card (Subgroup.closure ({a, b} : Set G)) = 24
  M_norm : ∀ m ∈ M, a * m * a⁻¹ ∈ M ∧ b * m * b⁻¹ ∈ M
  M_L : M ⊓ Subgroup.closure ({a, b} : Set G) = ⊥
  sigma_mem : σ ∈ M
  sigma_ord : orderOf σ = 3
  sigma_cent : ∀ g ∈ M ⊔ Subgroup.closure ({a, b} : Set G), g * σ = σ * g
  card_M : Nat.card M = 243
  exp3 : ∀ m ∈ M, m ^ 3 = 1
  comm_le : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ
  nonab : ∃ x ∈ M, ∃ y ∈ M, x * y ≠ y * x
  card_Z : Nat.card ↥(M ⊓ Subgroup.centralizer (M : Set G)) = 27
  z_inv : ∀ m ∈ M, z * m * z⁻¹ * m ∈ Subgroup.zpowers σ
  W_le : W ≤ M ⊓ Subgroup.centralizer {a}
  card_W : Nat.card W = 9
  W_inv : ∀ w ∈ W, z * w * z⁻¹ = w⁻¹
  w₁_mem : w₁ ∈ W ⊓ (M ⊓ Subgroup.centralizer (M : Set G))
  w₁_ne : w₁ ≠ 1
  w₂_mem : w₂ ∈ W
  w₂_not : w₂ ∉ M ⊓ Subgroup.centralizer (M : Set G)

end CFSG.GH74.QTGen4.Recog.G23.P7
