module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

structure Y6GData {G : Type} [Group G] (g t : G) (P M : Subgroup G) : Prop where
  g_order : orderOf g = 2
  t_order : orderOf t = 2
  comm : g * t = t * g
  t_ne_g : t ≠ g
  no_conj : ∀ x ∈ centralizer ({g} : Set G), x * t * x⁻¹ ≠ g * t
  D_eq : centralizer ({g} : Set G) ⊓ centralizer ({t} : Set G) = P ⊔ closure ({g, t} : Set G)
  P_inf : P ⊓ closure ({g, t} : Set G) = ⊥
  P_equiv : Nonempty (↥P ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)))
  P_four : ∀ p ∈ P, p ^ 4 = 1 → p ^ 2 = 1
  M_equiv : Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4)))
  M_cent : ∀ m ∈ M, g * m = m * g
  M_inv : ∀ m ∈ M, t * m * t⁻¹ = m⁻¹
  g_not_mem_M : g ∉ M

structure Y6CData {C : Type} [Group C] (g t : C) (P M : Subgroup C) : Prop where
  g_central : g ∈ center C
  g_order : orderOf g = 2
  t_order : orderOf t = 2
  t_ne_g : t ≠ g
  no_conj : ∀ x : C, x * t * x⁻¹ ≠ g * t
  D_eq : centralizer ({t} : Set C) = P ⊔ closure ({g, t} : Set C)
  P_inf : P ⊓ closure ({g, t} : Set C) = ⊥
  P_equiv : Nonempty (↥P ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)))
  P_four : ∀ p ∈ P, p ^ 4 = 1 → p ^ 2 = 1
  M_equiv : Nonempty (↥M ≃* (Fin 3 → Multiplicative (ZMod 4)))
  M_inv : ∀ m ∈ M, t * m * t⁻¹ = m⁻¹
  g_not_mem_M : g ∉ M

variable {G : Type} [Group G]

@[expose] def y6f4aG (g : G) : ↥(centralizer ({g} : Set G)) :=
  ⟨g, Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]⟩

@[expose] def y6f4aT (g t : G) (h : g * t = t * g) : ↥(centralizer ({g} : Set G)) :=
  ⟨t, Subgroup.mem_centralizer_iff.mpr fun x hx => by rw [Set.mem_singleton_iff.mp hx]; exact h⟩

instance y6f4a_zpowers_normal (g : G) : (zpowers (y6f4aG g)).Normal := by
  apply Subgroup.normal_of_le_center
  rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp x.2 g (Set.mem_singleton g)).symm

end CFSG.OddStandard.HigherRank.YamadaG23
