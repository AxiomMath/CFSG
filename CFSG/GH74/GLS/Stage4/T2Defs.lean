module

public import CFSG.GH74.GLS.Stage4.RestPre

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

structure T2N1 (G : Type) [Group G] where
  q₁ : ℕ
  q₂ : ℕ
  z : G
  S : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  H : Subgroup G
  X₁ : Subgroup G
  X₁' : Subgroup G
  X₂ : Subgroup G
  X₂' : Subgroup G
  w₁ : G
  w₂ : G

structure T2N2 (G : Type) [Group G] extends T2N1 G where
  F : Subgroup G

structure T2N3 (G : Type) [Group G] extends T2N2 G where
  a : G

structure T2N4 (G : Type) [Group G] extends T2N3 G where
  p : ℕ
  P₀ : Subgroup G
  P : Subgroup G

variable {G : Type} [Group G]

@[expose] def T2N3.u (N : T2N3 G) : G := N.a⁻¹ * N.z * N.a

@[expose] def T2N3.Nsub (N : T2N3 G) : Subgroup G :=
  Subgroup.closure ((N.H : Set G) ∪ {N.w₁, N.a⁻¹ * N.w₂ * N.a})

@[expose] def T2N4.toCh6 (N : T2N4 G) : Ch6Notation G where
  p := N.p
  q₁ := N.q₁
  q₂ := N.q₂
  z := N.z
  S := N.S
  K₁ := N.K₁
  K₂ := N.K₂
  F := N.F
  P₀ := N.P₀
  H := N.H
  P := N.P
  X₁ := N.X₁
  X₁' := N.X₁'
  X₂ := N.X₂
  X₂' := N.X₂'
  w₁ := N.w₁
  w₂ := N.w₂
  a := N.a

@[expose] def ActsAsConj (t : G) (K : Subgroup G) {F : Type} [Field F]
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (g : GL (Fin 2) F) : Prop :=
  ∀ x : ↥K, ∃ y : ↥K, (y : G) = t * (x : G) * t⁻¹ ∧
    ((e y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) *
        ((e x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)

structure Ch6Rem (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G) : Prop where
  comm_z : t * z = z * t
  sq : t * t = 1
  gen : K₁ ⊔ K₂ ⊔ zpowers t = oPrimeResidualOf 2 (centralizer ({z} : Set G))
  diag₁ : ∃ (e : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) (g : GL (Fin 2) F₁),
    ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₁ˣ) : F₁) ∧ ActsAsConj t K₁ e g
  diag₂ : ∃ (e : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (g : GL (Fin 2) F₂),
    ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₂ˣ) : F₂) ∧ ActsAsConj t K₂ e g

@[expose] def Ch6Num (q₁ q₂ : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ m : ℕ, q₁ = p ^ m) ∧ (∃ n : ℕ, q₂ = p ^ n) ∧ (q₁ = q₂ ∨ q₁ = q₂ ^ 3)

structure Ch6NumD (p q₁ q₂ : ℕ) : Prop where
  prime : p.Prime
  p_ne_two : p ≠ 2
  q₁_pow : ∃ m : ℕ, q₁ = p ^ m
  q₂_pow : ∃ n : ℕ, q₂ = p ^ n
  q_rel : q₁ = q₂ ∨ q₁ = q₂ ^ 3

structure Ch6Loc5 (N : T2N1 G) (u : G) : Prop where
  q₁_odd : Odd N.q₁
  q₂_odd : Odd N.q₂
  q₂_le : N.q₂ ≤ N.q₁
  q₁_ge : 5 ≤ N.q₁
  q₂_ge : 3 ≤ N.q₂
  q₁_pp : ∃ (p m : ℕ), p.Prime ∧ N.q₁ = p ^ m
  q₂_pp : ∃ (p m : ℕ), p.Prime ∧ N.q₂ = p ^ m
  z_ord : orderOf N.z = 2
  one_class : ∀ x : G, orderOf x = 2 → IsConj N.z x
  O2prime : pPrimeCore 2 ↥(centralizer ({N.z} : Set G)) = ⊥
  K_comm : ∀ x ∈ N.K₁, ∀ y ∈ N.K₂, x * y = y * x
  iso₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = N.q₁ ∧ Nonempty (↥N.K₁ ≃* SL2 F)
  iso₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = N.q₂ ∧ Nonempty (↥N.K₂ ≃* SL2 F)
  z_mem_K₁ : N.z ∈ N.K₁
  z_mem_K₂ : N.z ∈ N.K₂
  K_inter : N.K₁ ⊓ N.K₂ ≤ Subgroup.zpowers N.z
  u_ord : orderOf u = 2
  u_ne : u ≠ N.z
  u_comm : u * N.z = N.z * u
  S_pGroup : IsPGroup 2 ↥N.S
  S_sylow : ¬ 2 ∣ N.S.index
  z_mem_S : N.z ∈ N.S
  z_cent_S : ∀ s ∈ N.S, s * N.z = N.z * s
  u_mem_S : u ∈ N.S
  S_idx : (N.S ⊓ (N.K₁ ⊔ N.K₂)).relIndex N.S = 2
  w₁_memS : N.w₁ ∈ N.S
  w₂_memS : N.w₂ ∈ N.S
  K₁_eq : N.K₁ = N.X₁ ⊔ N.X₁'
  K₂_eq : N.K₂ = N.X₂ ⊔ N.X₂'
  card_X₁ : Nat.card ↥N.X₁ = N.q₁
  card_X₁' : Nat.card ↥N.X₁' = N.q₁
  card_X₂ : Nat.card ↥N.X₂ = N.q₂
  card_X₂' : Nat.card ↥N.X₂' = N.q₂
  X₁_comm : ∀ x ∈ N.X₁, ∀ y ∈ N.X₁, x * y = y * x
  X₁'_comm : ∀ x ∈ N.X₁', ∀ y ∈ N.X₁', x * y = y * x
  X₂_comm : ∀ x ∈ N.X₂, ∀ y ∈ N.X₂, x * y = y * x
  X₂'_comm : ∀ x ∈ N.X₂', ∀ y ∈ N.X₂', x * y = y * x
  X₁_exp : ∀ x ∈ N.X₁, x ^ N.q₁.minFac = 1
  X₁'_exp : ∀ x ∈ N.X₁', x ^ N.q₁.minFac = 1
  X₂_exp : ∀ x ∈ N.X₂, x ^ N.q₂.minFac = 1
  X₂'_exp : ∀ x ∈ N.X₂', x ^ N.q₂.minFac = 1
  X₁_ne : N.X₁ ≠ N.X₁'
  X₂_ne : N.X₂ ≠ N.X₂'
  H_comm : ∀ x ∈ N.H, ∀ y ∈ N.H, x * y = y * x
  z_mem_H : N.z ∈ N.H
  u_mem_H : u ∈ N.H
  H₁_eq : N.H ⊓ N.K₁ = centralizer ({u} : Set G) ⊓ N.K₁
  H₂_eq : N.H ⊓ N.K₂ = centralizer ({u} : Set G) ⊓ N.K₂
  H₁_cyc : IsCyclic ↥(N.H ⊓ N.K₁)
  H₂_cyc : IsCyclic ↥(N.H ⊓ N.K₂)
  card_H_K₁ : Nat.card ↥(N.H ⊓ N.K₁) = N.q₁ - 1
  card_H_K₂ : Nat.card ↥(N.H ⊓ N.K₂) = N.q₂ - 1
  H_idx : ((N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂)).relIndex N.H = 2
  H_le : N.H ≤ N.K₁ ⊔ N.K₂ ⊔ N.S
  H_not_le_K : ¬ N.H ≤ N.K₁ ⊔ N.K₂
  H_norm_X₁ : ∀ h ∈ N.H, ∀ x ∈ N.X₁, h * x * h⁻¹ ∈ N.X₁
  H_norm_X₁' : ∀ h ∈ N.H, ∀ x ∈ N.X₁', h * x * h⁻¹ ∈ N.X₁'
  H_norm_X₂ : ∀ h ∈ N.H, ∀ x ∈ N.X₂, h * x * h⁻¹ ∈ N.X₂
  H_norm_X₂' : ∀ h ∈ N.H, ∀ x ∈ N.X₂', h * x * h⁻¹ ∈ N.X₂'
  H_fpf₁ : ∀ h ∈ N.H ⊓ N.K₁, h ∉ Subgroup.zpowers N.z → ∀ x ∈ N.X₁, h * x * h⁻¹ = x → x = 1
  H_fpf₁' : ∀ h ∈ N.H ⊓ N.K₁, h ∉ Subgroup.zpowers N.z → ∀ x ∈ N.X₁', h * x * h⁻¹ = x → x = 1
  H_fpf₂ : ∀ h ∈ N.H ⊓ N.K₂, h ∉ Subgroup.zpowers N.z → ∀ x ∈ N.X₂, h * x * h⁻¹ = x → x = 1
  H_fpf₂' : ∀ h ∈ N.H ⊓ N.K₂, h ∉ Subgroup.zpowers N.z → ∀ x ∈ N.X₂', h * x * h⁻¹ = x → x = 1
  w₁_mem : N.w₁ ∈ N.K₁
  w₂_mem : N.w₂ ∈ N.K₂
  w₁_sq : N.w₁ * N.w₁ = N.z
  w₂_sq : N.w₂ * N.w₂ = N.z
  w₁_swap : ∀ x ∈ N.X₁, N.w₁ * x * N.w₁⁻¹ ∈ N.X₁'
  w₁_swap' : ∀ x ∈ N.X₁', N.w₁ * x * N.w₁⁻¹ ∈ N.X₁
  w₂_swap : ∀ x ∈ N.X₂, N.w₂ * x * N.w₂⁻¹ ∈ N.X₂'
  w₂_swap' : ∀ x ∈ N.X₂', N.w₂ * x * N.w₂⁻¹ ∈ N.X₂
  w₁_inv : ∀ h ∈ N.H ⊓ N.K₁, N.w₁ * h * N.w₁⁻¹ = h⁻¹
  w₂_inv : ∀ h ∈ N.H ⊓ N.K₂, N.w₂ * h * N.w₂⁻¹ = h⁻¹
  w₁_u : N.w₁ * u * N.w₁⁻¹ = u * N.z
  w₂_u : N.w₂ * u * N.w₂⁻¹ = u * N.z
  w₁_normH : N.w₁ ∈ normalizer (N.H : Set G)
  w₂_normH : N.w₂ ∈ normalizer (N.H : Set G)
  w₀_inv : ∀ h ∈ N.H, (N.w₁ * N.w₂) * h * (N.w₁ * N.w₂)⁻¹ = h⁻¹
  w₀_cent : (N.w₁ * N.w₂) * u = u * (N.w₁ * N.w₂)
  u_inv_X₁ : ∀ x ∈ N.X₁, u * x * u⁻¹ = x⁻¹
  u_inv_X₁' : ∀ x ∈ N.X₁', u * x * u⁻¹ = x⁻¹
  u_inv_X₂ : ∀ x ∈ N.X₂, u * x * u⁻¹ = x⁻¹
  u_inv_X₂' : ∀ x ∈ N.X₂', u * x * u⁻¹ = x⁻¹

structure Ch6F5 (N : T2N2 G) : Prop where
  F_def : N.F = (pPrimeCore 2 ↥(centralizer (N.S : Set G))).map (centralizer (N.S : Set G)).subtype
  F_odd : ∀ f ∈ N.F, Odd (orderOf f)
  F_comm : ∀ x ∈ N.F, ∀ y ∈ N.F, x * y = y * x
  F_inter_K : N.F ⊓ (N.K₁ ⊔ N.K₂) = ⊥
  C_le : centralizer ({N.z} : Set G) ≤ N.K₁ ⊔ N.K₂ ⊔ N.S ⊔ N.F
  centS : centralizer (N.S : Set G) = Subgroup.zpowers N.z ⊔ N.F
  F_normH : N.F ≤ normalizer (N.H : Set G)
  F_normX₁ : ∀ f ∈ N.F, ∀ x ∈ N.X₁, f * x * f⁻¹ ∈ N.X₁
  F_normX₁' : ∀ f ∈ N.F, ∀ x ∈ N.X₁', f * x * f⁻¹ ∈ N.X₁'
  F_normX₂ : ∀ f ∈ N.F, ∀ x ∈ N.X₂, f * x * f⁻¹ ∈ N.X₂
  F_normX₂' : ∀ f ∈ N.F, ∀ x ∈ N.X₂', f * x * f⁻¹ ∈ N.X₂'

structure Ch6Weyl (N : T2N3 G) : Prop where
  a_normH : N.a ∈ normalizer (N.H : Set G)
  a_cube : N.a ^ 3 ∈ N.H
  w₁_a : ∃ h ∈ N.H, N.w₁ * N.a * N.w₁⁻¹ = N.a⁻¹ * h
  w₂_a : ∃ h ∈ N.H, N.w₂ * N.a * N.w₂⁻¹ = N.a⁻¹ * h
  a_mem_N : N.a ∈ N.Nsub
  a_cycle : N.a⁻¹ * N.u * N.a = N.z * N.u
  F_normN : N.F ≤ normalizer (N.Nsub : Set G)

structure Ch6Sec5 (N : T2N3 G) (u : G) : Prop where
  loc : Ch6Loc5 N.toT2N2.toT2N1 u
  F5 : Ch6F5 N.toT2N2
  weyl : Ch6Weyl N
  u_eq : N.u = u

@[expose] def Ch6Notation.R₂ (D : Ch6Notation G) : Subgroup G :=
  CFSG.Open.pCoreOf D.p (normalizer (D.X₂ : Set G))

structure Ch6S6 (D : Ch6Notation G) : Prop where
  H_pPrime : ∀ h ∈ D.H, ¬ D.p ∣ orderOf h
  X₂_le_R₂ : D.X₂ ≤ D.R₂
  R₂_card : Nat.card ↥D.R₂ = D.q₁ ^ 2 * D.q₂ ^ 3
  R₂_center : ∀ y ∈ D.R₂, (∀ x ∈ D.R₂, x * y = y * x) ↔ y ∈ D.X₂
  R₂_comm : ∀ x ∈ D.R₂, ∀ y ∈ D.R₂, ⁅x, y⁆ ∈ D.X₂
  R₂_inv : ∀ r ∈ D.R₂, D.z * r * D.z⁻¹ * r ∈ D.X₂
  R₂_normH : ∀ h ∈ D.H, ∀ r ∈ D.R₂, h * r * h⁻¹ ∈ D.R₂
  K₁_normR₂ : ∀ x ∈ D.K₁, ∀ r ∈ D.R₂, x * r * x⁻¹ ∈ D.R₂
  K₁_irred : ∀ V : Subgroup G, D.X₂ ≤ V → V ≤ D.R₂ → (∀ x ∈ D.K₁, ∀ v ∈ V, x * v * x⁻¹ ∈ V) →
    V = D.X₂ ∨ V = D.R₂
  P_eq : D.P = D.R₂ ⊔ D.X₁
  P_pGroup : IsPGroup D.p ↥D.P
  P_card : Nat.card ↥D.P = D.q₁ ^ 3 * D.q₂ ^ 3
  P_normH : ∀ h ∈ D.H, ∀ x ∈ D.P, h * x * h⁻¹ ∈ D.P
  X₂_central : ∀ x ∈ D.X₂, ∀ y ∈ D.P, x * y = y * x
  P₀_le : D.P₀ ≤ D.F
  P₀_pGroup : IsPGroup D.p ↥D.P₀
  F_normB : D.F ≤ normalizer ((D.H ⊔ D.P : Subgroup G) : Set G)
  P₀_normP : D.P₀ ≤ normalizer (D.P : Set G)
  Sylow_PP₀ : ∃ T : Sylow D.p G, (T : Subgroup G) = D.P ⊔ D.P₀

structure Ch6Shape (D : Ch6Notation G) : Prop where
  shape : ∃ α β γ δ : Bool, D.Shape α β γ δ ∧
    centralizer ({D.z} : Set G) ⊓ D.P = D.X₁ ⊔ D.X₂ ∧
    centralizer ({D.u} : Set G) ⊓ D.P = conjBy D.a (D.A α ⊔ D.B β) ∧
    centralizer ({D.z * D.u} : Set G) ⊓ D.P = conjBy (D.a ^ 2) (D.A γ ⊔ D.B δ)
  inequiv : ∀ i j : ℤ, IsRoot 6 i → IsRoot 6 j → D.root i ≤ D.P → D.root j ≤ D.P → i ≠ j →
    ¬ HEquiv D.H (D.root i) (D.root j)
  comm_R : ∀ α β γ δ : Bool, D.Shape α β γ δ → ∀ S₁ ∈ D.Rfac α β γ δ, ∀ S₂ ∈ D.Rfac α β γ δ,
    ∀ x ∈ S₁, ∀ y ∈ S₂, ⁅x, y⁆ ∈ D.X₂

end CFSG.GH74.GLS.Stage4.Rest
