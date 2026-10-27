module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mul_eq_commutator_mul (x y : G) : x * y = ⁅x, y⁆ * (y * x) := by
  rw [commutatorElement_def]; group

private theorem conj_eq_of_comm {g h : G} (hgh : ⁅g, h⁆ = 1) : MulAut.conj g h = h := by
  rw [MulAut.conj_apply, (commutatorElement_eq_one_iff_mul_comm.mp hgh)]
  group

private theorem conj_eq_of_eq_z {g h z : G} (hgh : ⁅g, h⁆ = z) : MulAut.conj g h = z * h := by
  rw [MulAut.conj_apply, ← hgh, commutatorElement_def]
  group

private theorem commutatorElement_inv_eq_one {g h : G} (hgh : ⁅g, h⁆ = 1) : ⁅h, g⁆ = 1 := by
  rw [← commutatorElement_inv, hgh, inv_one]

private theorem commutatorElement_inv_eq_z {g h z : G} (hgh : ⁅g, h⁆ = z) (hz2 : z ^ 2 = 1) :
    ⁅h, g⁆ = z := by
  have hzz : z * z = 1 := by simpa [pow_two] using hz2
  rw [← commutatorElement_inv, hgh]
  exact mul_eq_one_iff_inv_eq.mp hzz

theorem y4_central_aut {a₁ b₁ a₂ b₂ z y : G} (hz2 : z ^ 2 = 1)
    (hza₁ : ⁅z, a₁⁆ = 1) (hzb₁ : ⁅z, b₁⁆ = 1) (hza₂ : ⁅z, a₂⁆ = 1) (hzb₂ : ⁅z, b₂⁆ = 1)
    (h₁ : ⁅a₁, b₁⁆ = z) (h₂ : ⁅a₂, b₂⁆ = z) (h₃ : ⁅a₁, a₂⁆ = 1) (h₄ : ⁅a₁, b₂⁆ = 1)
    (h₅ : ⁅b₁, a₂⁆ = 1) (h₆ : ⁅b₁, b₂⁆ = 1)
    (hy : ∀ a ∈ ({a₁, b₁, a₂, b₂} : Set G), ⁅y, a⁆ = 1 ∨ ⁅y, a⁆ = z) :
    ∃ c ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G),
      c⁻¹ * y ∈ centralizer ((closure {a₁, b₁, a₂, b₂} : Subgroup G) : Set G) := by
  classical
  let c : G := (if ⁅y, a₁⁆ = z then b₁ else 1) * (if ⁅y, b₁⁆ = z then a₁ else 1)
      * (if ⁅y, a₂⁆ = z then b₂ else 1) * (if ⁅y, b₂⁆ = z then a₂ else 1)
  have j_a1a1 : MulAut.conj a₁ a₁ = a₁ := conj_eq_of_comm (by simp)
  have j_b1b1 : MulAut.conj b₁ b₁ = b₁ := conj_eq_of_comm (by simp)
  have j_a2a2 : MulAut.conj a₂ a₂ = a₂ := conj_eq_of_comm (by simp)
  have j_b2b2 : MulAut.conj b₂ b₂ = b₂ := conj_eq_of_comm (by simp)
  have j_a1b1 : MulAut.conj a₁ b₁ = z * b₁ := conj_eq_of_eq_z h₁
  have j_b1a1 : MulAut.conj b₁ a₁ = z * a₁ := conj_eq_of_eq_z (commutatorElement_inv_eq_z h₁ hz2)
  have j_a2b2 : MulAut.conj a₂ b₂ = z * b₂ := conj_eq_of_eq_z h₂
  have j_b2a2 : MulAut.conj b₂ a₂ = z * a₂ := conj_eq_of_eq_z (commutatorElement_inv_eq_z h₂ hz2)
  have j_a1a2 : MulAut.conj a₁ a₂ = a₂ := conj_eq_of_comm h₃
  have j_a1b2 : MulAut.conj a₁ b₂ = b₂ := conj_eq_of_comm h₄
  have j_b1a2 : MulAut.conj b₁ a₂ = a₂ := conj_eq_of_comm h₅
  have j_b1b2 : MulAut.conj b₁ b₂ = b₂ := conj_eq_of_comm h₆
  have j_a2a1 : MulAut.conj a₂ a₁ = a₁ := conj_eq_of_comm (commutatorElement_inv_eq_one h₃)
  have j_b2a1 : MulAut.conj b₂ a₁ = a₁ := conj_eq_of_comm (commutatorElement_inv_eq_one h₄)
  have j_a2b1 : MulAut.conj a₂ b₁ = b₁ := conj_eq_of_comm (commutatorElement_inv_eq_one h₅)
  have j_b2b1 : MulAut.conj b₂ b₁ = b₁ := conj_eq_of_comm (commutatorElement_inv_eq_one h₆)
  have j_a1z : MulAut.conj a₁ z = z := conj_eq_of_comm (commutatorElement_inv_eq_one hza₁)
  have j_b1z : MulAut.conj b₁ z = z := conj_eq_of_comm (commutatorElement_inv_eq_one hzb₁)
  have j_a2z : MulAut.conj a₂ z = z := conj_eq_of_comm (commutatorElement_inv_eq_one hza₂)
  have j_b2z : MulAut.conj b₂ z = z := conj_eq_of_comm (commutatorElement_inv_eq_one hzb₂)
  have hmem : c ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
    have hf1 : (if ⁅y, a₁⁆ = z then b₁ else 1) ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
      by_cases h : ⁅y, a₁⁆ = z
      · rw [if_pos h]; exact Subgroup.subset_closure (by simp)
      · rw [if_neg h]; exact one_mem _
    have hf2 : (if ⁅y, b₁⁆ = z then a₁ else 1) ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
      by_cases h : ⁅y, b₁⁆ = z
      · rw [if_pos h]; exact Subgroup.subset_closure (by simp)
      · rw [if_neg h]; exact one_mem _
    have hf3 : (if ⁅y, a₂⁆ = z then b₂ else 1) ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
      by_cases h : ⁅y, a₂⁆ = z
      · rw [if_pos h]; exact Subgroup.subset_closure (by simp)
      · rw [if_neg h]; exact one_mem _
    have hf4 : (if ⁅y, b₂⁆ = z then a₂ else 1) ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by
      by_cases h : ⁅y, b₂⁆ = z
      · rw [if_pos h]; exact Subgroup.subset_closure (by simp)
      · rw [if_neg h]; exact one_mem _
    dsimp only [c]
    exact mul_mem (mul_mem (mul_mem hf1 hf2) hf3) hf4
  have hc1 : c * a₁ * c⁻¹ = (if ⁅y, a₁⁆ = z then z else 1) * a₁ := by
    rw [← MulAut.conj_apply]
    dsimp only [c]
    split_ifs <;>
      simp only [map_mul, map_one, one_mul, MulAut.mul_apply, MulAut.one_apply,
        j_a1a1, j_b1a1, j_a2a1, j_b2a1, j_a1z, j_b1z, j_a2z, j_b2z]
  have hc2 : c * b₁ * c⁻¹ = (if ⁅y, b₁⁆ = z then z else 1) * b₁ := by
    rw [← MulAut.conj_apply]
    dsimp only [c]
    split_ifs <;>
      simp only [map_mul, map_one, one_mul, MulAut.mul_apply, MulAut.one_apply,
        j_a1b1, j_b1b1, j_a2b1, j_b2b1, j_a1z, j_b1z, j_a2z, j_b2z]
  have hc3 : c * a₂ * c⁻¹ = (if ⁅y, a₂⁆ = z then z else 1) * a₂ := by
    rw [← MulAut.conj_apply]
    dsimp only [c]
    split_ifs <;>
      simp only [map_mul, map_one, one_mul, MulAut.mul_apply, MulAut.one_apply,
        j_a1a2, j_b1a2, j_a2a2, j_b2a2, j_a1z, j_b1z, j_a2z, j_b2z]
  have hc4 : c * b₂ * c⁻¹ = (if ⁅y, b₂⁆ = z then z else 1) * b₂ := by
    rw [← MulAut.conj_apply]
    dsimp only [c]
    split_ifs <;>
      simp only [map_mul, map_one, one_mul, MulAut.mul_apply, MulAut.one_apply,
        j_a1b2, j_b1b2, j_a2b2, j_b2b2, j_a1z, j_b1z, j_a2z, j_b2z]
  have hya1 : y * a₁ = (if ⁅y, a₁⁆ = z then z else 1) * a₁ * y := by
    rw [mul_eq_commutator_mul]
    by_cases h : ⁅y, a₁⁆ = z
    · rw [if_pos h, h]; group
    · rw [if_neg h, (hy a₁ (by simp)).resolve_right h]; group
  have hya2 : y * b₁ = (if ⁅y, b₁⁆ = z then z else 1) * b₁ * y := by
    rw [mul_eq_commutator_mul]
    by_cases h : ⁅y, b₁⁆ = z
    · rw [if_pos h, h]; group
    · rw [if_neg h, (hy b₁ (by simp)).resolve_right h]; group
  have hya3 : y * a₂ = (if ⁅y, a₂⁆ = z then z else 1) * a₂ * y := by
    rw [mul_eq_commutator_mul]
    by_cases h : ⁅y, a₂⁆ = z
    · rw [if_pos h, h]; group
    · rw [if_neg h, (hy a₂ (by simp)).resolve_right h]; group
  have hya4 : y * b₂ = (if ⁅y, b₂⁆ = z then z else 1) * b₂ * y := by
    rw [mul_eq_commutator_mul]
    by_cases h : ⁅y, b₂⁆ = z
    · rw [if_pos h, h]; group
    · rw [if_neg h, (hy b₂ (by simp)).resolve_right h]; group
  have hcomm1 : (c⁻¹ * y) * a₁ = a₁ * (c⁻¹ * y) := by
    calc (c⁻¹ * y) * a₁ = c⁻¹ * (y * a₁) := by group
      _ = c⁻¹ * ((if ⁅y, a₁⁆ = z then z else 1) * a₁ * y) := by rw [hya1]
      _ = a₁ * (c⁻¹ * y) := by rw [← hc1]; group
  have hcomm2 : (c⁻¹ * y) * b₁ = b₁ * (c⁻¹ * y) := by
    calc (c⁻¹ * y) * b₁ = c⁻¹ * (y * b₁) := by group
      _ = c⁻¹ * ((if ⁅y, b₁⁆ = z then z else 1) * b₁ * y) := by rw [hya2]
      _ = b₁ * (c⁻¹ * y) := by rw [← hc2]; group
  have hcomm3 : (c⁻¹ * y) * a₂ = a₂ * (c⁻¹ * y) := by
    calc (c⁻¹ * y) * a₂ = c⁻¹ * (y * a₂) := by group
      _ = c⁻¹ * ((if ⁅y, a₂⁆ = z then z else 1) * a₂ * y) := by rw [hya3]
      _ = a₂ * (c⁻¹ * y) := by rw [← hc3]; group
  have hcomm4 : (c⁻¹ * y) * b₂ = b₂ * (c⁻¹ * y) := by
    calc (c⁻¹ * y) * b₂ = c⁻¹ * (y * b₂) := by group
      _ = c⁻¹ * ((if ⁅y, b₂⁆ = z then z else 1) * b₂ * y) := by rw [hya4]
      _ = b₂ * (c⁻¹ * y) := by rw [← hc4]; group
  refine ⟨c, hmem, ?_⟩
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro h hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact hcomm1.symm
  · exact hcomm2.symm
  · exact hcomm3.symm
  · exact hcomm4.symm

end CFSG.OddStandard.HigherRank.YamadaG23
