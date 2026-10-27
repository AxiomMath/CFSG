module

public import CFSG.GH74.GLS.LU.Local.FiveBundles

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

structure Five66W (z t u : G) (K₁ K₂ H : Subgroup G) (w₁ : G) : Prop where
  z_mem : z ∈ H
  u_mem : u ∈ H
  H_cent : ∀ h ∈ H, h * z = z * h ∧ h * u = u * h
  H_iso : Nonempty (↥H ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
  H_normK : ∀ h ∈ H, cjL h K₁ = K₁ ∧ cjL h K₂ = K₂
  t_normH : cjL t H = H
  CU_two : IsPGroup 2 ↥(centralizer ((UU z u : Subgroup G) : Set G))
  w₁_mem : w₁ ∈ K₁
  w₁_sq : w₁ ^ 2 = z
  w₁_u : w₁ * u * w₁⁻¹ = u * z
  t_normL : ∀ g : G, g * z * g⁻¹ = u →
    cjL t (cjL g K₁) = cjL g K₁ ∧ cjL t (cjL g K₂) = cjL g K₂

structure Five66N (z u : G) (H : Subgroup G) : Prop where
  N_normH : ∀ n ∈ NN z u, cjL n H = H
  N_quot : ∃ _ : (H.subgroupOf (NN z u)).Normal,
    Nonempty (↥(NN z u) ⧸ H.subgroupOf (NN z u) ≃* Equiv.Perm (Fin 4))
  N_trans : ∀ x ∈ UU z u, x ≠ 1 → ∀ y ∈ UU z u, y ≠ 1 → ∃ n ∈ NN z u, n * x * n⁻¹ = y
  N_ord : ∀ n ∈ NN z u, orderOf n = 3 ∨ IsPGroup 2 ↥(zpowers n)

theorem Five66.toW {z t u : G} {K₁ K₂ H : Subgroup G} {w₁ : G} (h : Five66 z t u K₁ K₂ H w₁) :
    Five66W z t u K₁ K₂ H w₁ :=
  ⟨h.z_mem, h.u_mem, h.H_cent, h.H_iso, h.H_normK, h.t_normH, h.CU_two, h.w₁_mem, h.w₁_sq, h.w₁_u,
    h.t_normL⟩

theorem Five66.ofWN {z t u : G} {K₁ K₂ H : Subgroup G} {w₁ : G} (h : Five66W z t u K₁ K₂ H w₁)
    (n : Five66N z u H) : Five66 z t u K₁ K₂ H w₁ :=
  ⟨h.z_mem, h.u_mem, h.H_cent, h.H_iso, h.H_normK, h.t_normH, h.CU_two, n.N_normH, n.N_quot,
    n.N_trans, n.N_ord, h.w₁_mem, h.w₁_sq, h.w₁_u, h.t_normL⟩

structure Five82W (z t u : G) (K₁ K₂ H : Subgroup G) (w₁ : G) (X₁ : Subgroup G) : Prop where
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

structure Five82N (H : Subgroup G) : Prop where
  no_inv_sub : ∀ Y : Subgroup G, (∀ y ∈ Y, ¬ 2 ∣ orderOf y ∧ ¬ 5 ∣ orderOf y) →
    (∀ h ∈ H, cjL h Y = Y) → Y = ⊥

theorem Five82.toW {z t u : G} {K₁ K₂ H : Subgroup G} {w₁ : G} {X₁ : Subgroup G}
    (h : Five82 z t u K₁ K₂ H w₁ X₁) : Five82W z t u K₁ K₂ H w₁ X₁ :=
  ⟨h.X₁_syl, h.X₁_card, h.H_normX₁, h.K₁_gen, h.card_C, h.T_syl, h.C0_struct, h.NC_X2, h.CC_X2,
    h.NC_X, h.syl_inv, h.X_inv_sub⟩

theorem Five82.ofWN {z t u : G} {K₁ K₂ H : Subgroup G} {w₁ : G} {X₁ : Subgroup G}
    (h : Five82W z t u K₁ K₂ H w₁ X₁) (n : Five82N H) : Five82 z t u K₁ K₂ H w₁ X₁ :=
  ⟨h.X₁_syl, h.X₁_card, h.H_normX₁, h.K₁_gen, h.card_C, h.T_syl, h.C0_struct, h.NC_X2, h.CC_X2,
    h.NC_X, h.syl_inv, h.X_inv_sub, n.no_inv_sub⟩

end CFSG.GH74.GLS.LU.Local.Five
