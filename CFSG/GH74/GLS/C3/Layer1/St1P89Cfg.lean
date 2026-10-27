module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm6

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

structure Cfg89T (G : Type) [Group G] [Finite G] (T P Q : Subgroup G) (u z x f r s : G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  rank4 : pRank 2 G = 4
  sylowT : IsSylowOf 2 T (centralizer ({u} : Set G))
  x_ord : orderOf x = 2
  x_not_star : ¬ IsStar2 x
  P_le : P ≤ T
  Q_le : Q ≤ T
  P_norm : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P
  Q_norm : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q
  PQ_comm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  PQ_inf : ∀ g : G, g ∈ P → g ∈ Q → g = 1
  r_mem : r ∈ P
  s_mem : s ∈ P
  r4 : r ^ 4 = 1
  s2 : s ^ 2 = 1
  srs : s * r * s⁻¹ = r⁻¹
  r2_ne : r ^ 2 ≠ 1
  z_eq : z = r ^ 2
  P_gen : ∀ p ∈ P, ∃ i j : ℕ, p = r ^ i * s ^ j
  u_mem : u ∈ Q
  u2 : u ^ 2 = 1
  u_ne : u ≠ 1
  Q_inv : ∀ q ∈ Q, q ^ 2 = 1 → q = 1 ∨ q = u
  u_central : ∀ t ∈ T, t * u = u * t
  f_mem : f ∈ T
  f2 : f ^ 2 = 1
  f_cent : ∀ p ∈ P, f * p = p * f
  f_not : ∀ q ∈ Q, ∀ i : ℕ, f ≠ q * z ^ i
  x_mem : x ∈ T
  x2 : x ^ 2 = 1
  x_r : x * r * x⁻¹ = r⁻¹
  x_s : x * s * x⁻¹ = r * s ∨ x * s * x⁻¹ = r ^ 3 * s
  T_gen : ∀ t ∈ T, ∃ p ∈ P, ∃ q ∈ Q, ∃ i j : ℕ, t = p * q * f ^ i * x ^ j
  CTP : ∀ t ∈ T, (∀ p ∈ P, t * p = p * t) → ∃ i : ℕ, ∃ q ∈ Q, ∃ j : ℕ, t = z ^ i * q * f ^ j
  ZTQ : ∀ t ∈ T, (∀ t' ∈ T, t * t' * t⁻¹ * t'⁻¹ ∈ Q) → ∃ i : ℕ, ∃ q ∈ Q, t = z ^ i * q
  xf : ∃ q ∈ Q, x * f * x⁻¹ = z * q * f

structure Cfg89S (G : Type) [Group G] [Finite G] (T : Subgroup G) (u : G) (S : Subgroup G) (a : G) : Prop where
  sylowS : IsSylowOf 2 S ⊤
  T_le : T ≤ S
  a_mem : a ∈ S
  a_nmem : a ∉ T
  S_split : ∀ g ∈ S, g ∈ T ∨ a⁻¹ * g ∈ T
  T_norm : ∀ g ∈ S, ∀ t ∈ T, g * t * g⁻¹ ∈ T
  T_cent : ∀ g ∈ S, g * u = u * g → g ∈ T
  Zcyc : IsCyclic ↥(centerIn S)

end CFSG.GH74.GLS.C3.Layer1.P89
