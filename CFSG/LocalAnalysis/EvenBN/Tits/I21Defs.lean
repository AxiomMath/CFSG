module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open
open scoped MatrixGroups

@[expose] def sec622N : ℕ := 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127

@[expose] def Sec622T1 {G : Type*} [Group G] (u : G) : Prop :=
  ∃ A : Subgroup G, A.Normal ∧ IsPGroup 2 A ∧ u ^ 2 ∈ A

structure Sec622Bar (G : Type*) [Group G] (t u x : G) : Prop where
  secTwo : SecTwoHyp G t u
  oddCore : standardComponentOddCore G = ⊥
  comm_tx : t * x = x * t
  conj_ux : u * x * u⁻¹ = x ^ 2
  x_cases : x = 1 ∨ orderOf x = 5
  cent : centralizer ({t} : Set G) = closure {t, u, x}
  card_dvd : Nat.card G ∣ sec622N
  exp_two : ∀ g : G, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1

@[expose] def IsPSLTwo (L : Type*) [Group L] (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧ Nonempty (L ≃* PSL(2, F))

@[expose] def Sec622UniqueInv {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, orderOf a = 2 → orderOf b = 2 → a = b

@[expose] def Sec622Order16 {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  Nat.card M = 16 ∧ (∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) ∧
    ∃ c ∈ M, orderOf c = 4 ∧ ∀ m ∈ M, m * c = c * m

@[expose] def Sec622CentralInv {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  (∀ e ∈ M, e ^ 2 = 1 → ∀ m ∈ M, m * e = e * m) ∧
    ∃ z₀ : G, orderOf z₀ = 2 ∧ (∀ m ∈ M, m ^ 2 = 1 ∨ m ^ 2 = z₀) ∧ ∃ m ∈ M, m ^ 2 = z₀

@[expose] def Sec622ProdDihedral {G : Type*} [Group G] (M : Subgroup G) (n : ℕ) : Prop :=
  3 ≤ n ∧ ∃ c r s : G, orderOf c = 2 ∧ orderOf r = 2 ^ (n - 1) ∧ orderOf s = 2 ∧
    s * r * s⁻¹ = r⁻¹ ∧ c * r = r * c ∧ c * s = s * c ∧ M = closure {c, r, s} ∧
    c ∉ closure {r, s}

structure TwoGroupShape {G : Type*} [Group G] (P : Subgroup G) (t z : G) (n : ℕ) (x u₀ : G)
    (T : Subgroup G) : Prop where
  three_le : 3 ≤ n
  ord_x : orderOf x = 2 ^ (n - 1)
  inv_x : t * x * t⁻¹ = x⁻¹
  z_eq : x ^ (2 ^ (n - 2)) = z
  ord_u : orderOf u₀ = 4
  sq_u : u₀ ^ 2 = z
  comm_ut : u₀ * t = t * u₀
  comm_ux : u₀ * x = x * u₀
  inf_eq : zpowers u₀ ⊓ closure {t, x} = zpowers z
  T_eq : T = closure {t, x, u₀}
  T_le : T ≤ P
  T_idx : T.relIndex P ∣ 2
  R_le : centralizer ({t} : Set G) ⊓ P ≤ T
  U_norm : ∀ p ∈ P, ∀ v ∈ zpowers u₀, p * v * p⁻¹ ∈ zpowers u₀
  U_central : ∀ s ∈ T, s * u₀ = u₀ * s
  class_le_D : ∀ g : G, g * t * g⁻¹ ∈ P → g * t * g⁻¹ ∈ closure {t, x}
  D_eq : closure {s : G | s ∈ P ∧ ∃ g : G, g * t * g⁻¹ = s} = closure {t, x}
  quot : ∃ (_ : ((zpowers u₀).subgroupOf P).Normal),
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((P ⧸ (zpowers u₀).subgroupOf P) ≃* DihedralGroup (2 ^ m))) ∨
      ∃ k : ℕ, 4 ≤ k ∧ Nonempty ((P ⧸ (zpowers u₀).subgroupOf P) ≃* SemidihedralGroup k)

end CFSG.LocalAnalysis.EvenBN.Tits
