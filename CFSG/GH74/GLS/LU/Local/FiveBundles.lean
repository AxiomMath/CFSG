module

public import CFSG.GH74.GLS.LU.Local.A3
public import CFSG.GH74.GLS.LU.Local.FiveDef

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

@[expose] def LUA3Five' : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ p f : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ f →
    p ^ f = 5 → ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
      A3Hyp G p f z S K₁ K₂ t u → LUEps G (p ^ f) 1 z K₁ u → FiveExtra G z S →
        A3CoreLin G p f z K₁ K₂ u

end CFSG.GH74.GLS.LU.Local

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

abbrev cjL (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

@[expose] def IsSylowIn (p : ℕ) (P M : Subgroup G) : Prop :=
  P ≤ M ∧ IsPGroup p ↥P ∧ ¬ p ∣ (P.subgroupOf M).index

@[expose] def IsElemAb (p : ℕ) (E : Subgroup G) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ p = 1

abbrev UU (z u : G) : Subgroup G := zpowers z ⊔ zpowers u

abbrev TT (z t : G) : Subgroup G := zpowers z ⊔ zpowers t

abbrev NN (z u : G) : Subgroup G := normalizer ((UU z u : Subgroup G) : Set G)

abbrev XB (t : G) (X₁ : Subgroup G) : Subgroup G := cjL t X₁

abbrev XX (t : G) (X₁ : Subgroup G) : Subgroup G := X₁ ⊔ XB t X₁

abbrev XZ (t : G) (X₁ : Subgroup G) : Subgroup G := XX t X₁ ⊓ centralizer ({t} : Set G)

abbrev CZ (t : G) (X₁ : Subgroup G) : Subgroup G := centralizer ((XZ t X₁ : Subgroup G) : Set G)

abbrev X3 (v : G) (X₁ : Subgroup G) : Subgroup G := cjL v X₁
abbrev X4 (v t : G) (X₁ : Subgroup G) : Subgroup G := cjL v (XB t X₁)
abbrev X5 (v w₁ : G) (X₁ : Subgroup G) : Subgroup G := cjL w₁ (X3 v X₁)
abbrev X6 (v t w₁ : G) (X₁ : Subgroup G) : Subgroup G := cjL w₁ (X4 v t X₁)

structure FiveCtx (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G)
    (K₁ K₂ : Subgroup G) (t u : G) : Prop where
  simple : IsKProperSimple G
  prime : p.Prime
  odd : p ≠ 2
  pf : p ^ f = 5
  hyp : A3Hyp G p f z S K₁ K₂ t u
  eps : LUEps G (p ^ f) 1 z K₁ u
  extra : FiveExtra G z S

abbrev EE (v t w₁ : G) (X₁ : Subgroup G) : Subgroup G :=
  XB t X₁ ⊔ X4 v t X₁ ⊔ X6 v t w₁ X₁
abbrev DD (v w₁ : G) (X₁ : Subgroup G) : Subgroup G := X₁ ⊔ X3 v X₁ ⊔ X5 v w₁ X₁

abbrev RR (t : G) (X₁ : Subgroup G) : Subgroup G :=
  CFSG.Assembly.pCoreOf 5 (normalizer ((XB t X₁ : Subgroup G) : Set G))

structure Five66 (z t u : G) (K₁ K₂ H : Subgroup G) (w₁ : G) : Prop where
  z_mem : z ∈ H
  u_mem : u ∈ H
  H_cent : ∀ h ∈ H, h * z = z * h ∧ h * u = u * h
  H_iso : Nonempty (↥H ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
  H_normK : ∀ h ∈ H, cjL h K₁ = K₁ ∧ cjL h K₂ = K₂
  t_normH : cjL t H = H
  CU_two : IsPGroup 2 ↥(centralizer ((UU z u : Subgroup G) : Set G))
  N_normH : ∀ n ∈ NN z u, cjL n H = H
  N_quot : ∃ _ : (H.subgroupOf (NN z u)).Normal,
    Nonempty (↥(NN z u) ⧸ H.subgroupOf (NN z u) ≃* Equiv.Perm (Fin 4))
  N_trans : ∀ x ∈ UU z u, x ≠ 1 → ∀ y ∈ UU z u, y ≠ 1 → ∃ n ∈ NN z u, n * x * n⁻¹ = y
  N_ord : ∀ n ∈ NN z u, orderOf n = 3 ∨ IsPGroup 2 ↥(zpowers n)
  w₁_mem : w₁ ∈ K₁
  w₁_sq : w₁ ^ 2 = z
  w₁_u : w₁ * u * w₁⁻¹ = u * z
  t_normL : ∀ g : G, g * z * g⁻¹ = u →
    cjL t (cjL g K₁) = cjL g K₁ ∧ cjL t (cjL g K₂) = cjL g K₂

structure Five82 (z t u : G) (K₁ K₂ H : Subgroup G) (w₁ : G) (X₁ : Subgroup G) : Prop where
  X₁_syl : IsSylowIn 5 X₁ K₁
  X₁_card : Nat.card ↥X₁ = 5
  H_normX₁ : ∀ h ∈ H, cjL h X₁ = X₁
  K₁_gen : Subgroup.closure ((X₁ : Set G) ∪ {w₁}) = K₁
  card_C : Nat.card ↥(centralizer ({z} : Set G)) = 28800
  T_syl : IsSylowIn 2 (TT z t) (CZ t X₁)
  C0_struct : ∀ s ∈ TT z t, s ≠ 1 → ∃ Xs : Subgroup G, Xs ≤ CZ t X₁ ∧ IsElemAb 5 Xs ∧
    Nat.card ↥Xs = 25 ∧ (∀ x ∈ Xs, u * x * u⁻¹ = x⁻¹) ∧
    centralizer ({s} : Set G) ⊓ CZ t X₁ = Xs ⊔ TT z t ∧ Xs ⊓ TT z t = ⊥ ∧
    ∀ g ∈ centralizer ({s} : Set G) ⊓ CZ t X₁, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs
  NC_X2 : normalizer ((XB t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
    XB t X₁ ⊔ K₁ ⊔ H
  CC_X2 : centralizer ((XB t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) = XB t X₁ ⊔ K₁
  NC_X : normalizer ((XX t X₁ : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
    XX t X₁ ⊔ H ⊔ zpowers t
  syl_inv : ∀ R : Subgroup G, IsSylowIn 5 R (centralizer ({z} : Set G)) → (∀ h ∈ H, cjL h R = R) →
    ∃ w ∈ zpowers w₁ ⊔ zpowers (t * w₁ * t⁻¹), R = cjL w (XX t X₁)
  X_inv_sub : ∀ A : Subgroup G, A ≤ XX t X₁ → Nat.card ↥A = 5 → (∀ h ∈ H, cjL h A = A) →
    A = X₁ ∨ A = XB t X₁
  no_inv_sub : ∀ Y : Subgroup G, (∀ y ∈ Y, ¬ 2 ∣ orderOf y ∧ ¬ 5 ∣ orderOf y) →
    (∀ h ∈ H, cjL h Y = Y) → Y = ⊥

structure Five83 (z t u : G) (H X₁ Y : Subgroup G) : Prop where
  Y_card : Nat.card ↥Y = 25
  Y_ab : IsElemAb 5 Y
  XY_ab : IsElemAb 5 (XX t X₁ ⊔ Y)
  XY_card : Nat.card ↥(XX t X₁ ⊔ Y) = 5 ^ 4
  XY_disj : XX t X₁ ⊓ Y = ⊥
  W_eq : pPrimeCoreOf 2 (CZ t X₁) = XX t X₁ ⊔ Y
  u_inv : ∀ w ∈ XX t X₁ ⊔ Y, u * w * u⁻¹ = w⁻¹
  Y_syl : IsSylowIn 5 Y (centralizer ({z * u} : Set G))
  Y_H : ∀ h ∈ H, cjL h Y = Y
  CY_t : Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) = 5
  C0_five : (Nat.card ↥(CZ t X₁)).factorization 5 ≤ 5

structure Five84 (z t u : G) (H X₁ Y : Subgroup G) (v : G) : Prop where
  v_N : v ∈ NN z u
  v_two : IsPGroup 2 ↥(zpowers v)
  v_sq : v ^ 2 ∈ H
  v_z : v * z * v⁻¹ = z * u
  v_zu : v * (z * u) * v⁻¹ = z
  v_X : cjL v (XX t X₁) = Y
  v_Y : cjL v Y = XX t X₁

structure Five85 (z t u : G) (K₁ K₂ H : Subgroup G) (w₁ : G) (X₁ Y : Subgroup G) (v : G) : Prop where
  N_X2 : normalizer ((XB t X₁ : Subgroup G) : Set G) = RR t X₁ ⊔ K₁ ⊔ H
  R_eq : RR t X₁ = XB t X₁ ⊔ Y ⊔ cjL w₁ Y
  R_card : Nat.card ↥(RR t X₁) = 5 ^ 5
  Yw_eq : cjL w₁ Y = centralizer ({u} : Set G) ⊓ RR t X₁
  Yw_ab : IsElemAb 5 (cjL w₁ Y) ∧ Nat.card ↥(cjL w₁ Y) = 25
  z_inv : ∀ r ∈ RR t X₁, z * r * z⁻¹ * r ∈ XB t X₁
  R_cl2 : ∀ r ∈ RR t X₁, ∀ s ∈ RR t X₁, r * s * r⁻¹ * s⁻¹ ∈ XB t X₁
  place : ∃ g : G, g * z * g⁻¹ = u ∧
    ((X5 v w₁ X₁ ≤ cjL g K₁ ∧ X6 v t w₁ X₁ ≤ cjL g K₂) ∨
      (X5 v w₁ X₁ ≤ cjL g K₂ ∧ X6 v t w₁ X₁ ≤ cjL g K₁))

structure Five86 (t : G) (w₁ : G) (X₁ : Subgroup G) (v : G) : Prop where
  X6_v : cjL v (X6 v t w₁ X₁) = X6 v t w₁ X₁
  X5_tv : cjL (t * v) (X5 v w₁ X₁) = X5 v w₁ X₁
  X5_ne : cjL v (X5 v w₁ X₁) ≠ X5 v w₁ X₁

structure Five87 (t : G) (H : Subgroup G) (w₁ : G) (X₁ : Subgroup G) (v : G) : Prop where
  E_ab : IsElemAb 5 (EE v t w₁ X₁)
  E_card : Nat.card ↥(EE v t w₁ X₁) = 5 ^ 3
  E_H : ∀ h ∈ H, cjL h (EE v t w₁ X₁) = EE v t w₁ X₁
  D_card : Nat.card ↥(DD v w₁ X₁) = 5 ^ 3
  ED_disj : EE v t w₁ X₁ ⊓ DD v w₁ X₁ = ⊥
  ED_eq : EE v t w₁ X₁ ⊔ DD v w₁ X₁ = RR t X₁ ⊔ X₁
  ED_card : Nat.card ↥(EE v t w₁ X₁ ⊔ DD v w₁ X₁) = 5 ^ 6

structure Five88 (z t u : G) (K₁ K₂ : Subgroup G) (w₁ : G) (X₁ : Subgroup G) (v : G)
    (L' : Subgroup G) : Prop where
  C_E : centralizer ((EE v t w₁ X₁ : Subgroup G) : Set G) = EE v t w₁ X₁
  L'_N : L' ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)
  L'_disj : EE v t w₁ X₁ ⊓ L' = ⊥
  L'_sup : EE v t w₁ X₁ ⊔ L' = normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)
  L'_iso : Nonempty (SL(3, ZMod 5) ≃* ↥L')
  U_le : UU z u ≤ L'
  K₁_N : K₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)
  L_N : ∀ g : G, g * z * g⁻¹ = u → ∀ A : Subgroup G, (A = K₁ ∨ A = K₂) →
    X5 v w₁ X₁ ≤ cjL g A → cjL g A ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)

end CFSG.GH74.GLS.LU.Local.Five
