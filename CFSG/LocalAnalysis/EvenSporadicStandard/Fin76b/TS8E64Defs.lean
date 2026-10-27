module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HAut

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OE64

structure IsKlein {G : Type*} [Group G] (B : Subgroup G) (b₁ b₂ : G) : Prop where
  mem₁ : b₁ ∈ B
  mem₂ : b₂ ∈ B
  sq₁ : b₁ * b₁ = 1
  sq₂ : b₂ * b₂ = 1
  comm : b₁ * b₂ = b₂ * b₁
  ne₁ : b₁ ≠ 1
  ne₂ : b₂ ≠ 1
  ne₁₂ : b₁ ≠ b₂

namespace IsKlein

variable {G : Type*} [Group G] {B : Subgroup G} {b₁ b₂ : G} (k : IsKlein B b₁ b₂)

include k

theorem cases {g : G} (hg : g ∈ closure ({b₁, b₂} : Set G)) :
    g = 1 ∨ g = b₁ ∨ g = b₂ ∨ g = b₁ * b₂ :=
  E613.closure_pair_subset k.sq₁ k.sq₂ k.comm hg

omit k in
theorem b₁_mem_grp : b₁ ∈ closure ({b₁, b₂} : Set G) := subset_closure (by simp)

omit k in
theorem b₂_mem_grp : b₂ ∈ closure ({b₁, b₂} : Set G) := subset_closure (by simp)

theorem grp_le : closure ({b₁, b₂} : Set G) ≤ B := by
  rw [closure_le]
  rintro g (rfl | rfl)
  · exact k.mem₁
  · exact k.mem₂

theorem prod_mem : b₁ * b₂ ∈ B := mul_mem k.mem₁ k.mem₂

theorem prod_sq : (b₁ * b₂) * (b₁ * b₂) = 1 := by
  calc (b₁ * b₂) * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
    _ = b₁ * (b₁ * b₂) * b₂ := by rw [← k.comm]
    _ = (b₁ * b₁) * (b₂ * b₂) := by group
    _ = 1 := by rw [k.sq₁, k.sq₂, one_mul]

theorem prod_ne_one : b₁ * b₂ ≠ 1 := by
  intro h
  apply k.ne₁₂
  have h1 : b₁ = b₂⁻¹ := mul_eq_one_iff_eq_inv.1 h
  rw [h1]
  exact inv_eq_of_mul_eq_one_right k.sq₂

theorem sq_grp {g : G} (hg : g ∈ closure ({b₁, b₂} : Set G)) : g * g = 1 := by
  rcases k.cases hg with rfl | rfl | rfl | rfl
  · simp
  · exact k.sq₁
  · exact k.sq₂
  · exact k.prod_sq

theorem comm_grp {g g' : G} (hg : g ∈ closure ({b₁, b₂} : Set G))
    (hg' : g' ∈ closure ({b₁, b₂} : Set G)) : g * g' = g' * g := by
  have h1 : closure ({b₁, b₂} : Set G) ≤
      centralizer ((closure ({b₁, b₂} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure, closure_le]
    rintro g (rfl | rfl)
    · exact mem_centralizer_iff.2 (by rintro h (rfl | rfl); exacts [rfl, k.comm.symm])
    · exact mem_centralizer_iff.2 (by rintro h (rfl | rfl); exacts [k.comm, rfl])
  exact mem_centralizer_iff.1 (h1 hg') g hg

end IsKlein

section Klein

variable {G : Type*} [Group G]

@[expose] def genP (b₁ b₂ w₀ : G) : List G :=
  [1 * w₀ * 1⁻¹, b₁ * w₀ * b₁⁻¹, b₂ * w₀ * b₂⁻¹, (b₁ * b₂) * w₀ * (b₁ * b₂)⁻¹]

@[expose] def P1 (α b₁ b₂ w₀ : G) : Subgroup G := closure ({α} ∪ {x | x ∈ genP b₁ b₂ w₀})

theorem mem_genP {b₁ b₂ w₀ x : G} :
    x ∈ genP b₁ b₂ w₀ ↔ ∃ g, (g = 1 ∨ g = b₁ ∨ g = b₂ ∨ g = b₁ * b₂) ∧ x = g * w₀ * g⁻¹ := by
  constructor
  · intro hx
    simp only [genP, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, Or.inl rfl, rfl⟩
    · exact ⟨b₁, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨b₂, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨b₁ * b₂, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  · rintro ⟨g, hg, rfl⟩
    rcases hg with rfl | rfl | rfl | rfl <;> simp [genP]

theorem alpha_mem_P1 (α b₁ b₂ w₀ : G) : α ∈ P1 α b₁ b₂ w₀ := subset_closure (Or.inl rfl)

theorem omega_mem_P1 {B : Subgroup G} {b₁ b₂ : G} (k : IsKlein B b₁ b₂) (α w₀ : G) {g : G}
    (hg : g ∈ closure ({b₁, b₂} : Set G)) : g * w₀ * g⁻¹ ∈ P1 α b₁ b₂ w₀ := by
  refine subset_closure (Or.inr ?_)
  rw [Set.mem_ofPred_eq, mem_genP]
  exact ⟨g, k.cases hg, rfl⟩

@[expose] def P2 (P : Subgroup G) (z : G) : Subgroup G := P.comap (MulAut.conj z).toMonoidHom

theorem mem_P2 {P : Subgroup G} {z p : G} : p ∈ P2 P z ↔ z * p * z⁻¹ ∈ P := Iff.rfl

theorem mem_grp_of {b₁ b₂ b : G} (hb : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) :
    b ∈ closure ({b₁, b₂} : Set G) := by
  rcases hb with h | h | h <;> rw [h]
  exacts [IsKlein.b₁_mem_grp, IsKlein.b₂_mem_grp,
    mul_mem IsKlein.b₁_mem_grp IsKlein.b₂_mem_grp]

end Klein

end OE64

end CFSG.EvenSporadicStandard.Fin76b
