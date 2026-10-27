module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Prelude
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G]

structure HBase (G : Type*) [Group G] [Finite G] (x : G) (S T P Q Rd F : Subgroup G) :
    Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  x_sq : x * x = 1
  x_ne_one : x ≠ 1
  S_sylow : IsSylow2In S ⊤
  T_sylow : IsSylow2In T (Subgroup.centralizer ({x} : Set G))
  T_le_S : T ≤ S
  extremal : ∀ s ∈ S, s * x = x * s → s ∈ T
  rank_le : Rank2Le (Subgroup.centralizer ({x} : Set G)) 3
  rank_ge : ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({x} : Set G) ∧ IsElemAb2 E ∧
    Nat.card E = 8
  P_normal : NormalIn P T
  Q_normal : NormalIn Q T
  Rd_normal : NormalIn Rd T
  PQ_disjoint : P ⊓ Q = ⊥
  PQ_comm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  x_mem_Q : x ∈ Q
  R_le_Rd : P ⊔ Q ≤ Rd
  R_index_le_two : (P ⊔ Q).relIndex Rd ≤ 2
  F_le_T : F ≤ T
  Q_le_F : Q ≤ F
  F_inf_Rd : F ⊓ Rd = Q
  nonsolv : ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set G))

structure HZ (T P : Subgroup G) (z : G) : Prop where
  z_mem_P : z ∈ P
  z_sq : z * z = 1
  z_ne_one : z ≠ 1
  z_central : ∀ t ∈ T, z * t = t * z

structure HU (S T U : Subgroup G) : Prop where
  four : IsFour U
  normal : NormalIn U S
  le_T : U ≤ T

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
