module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem ncard_tF_cases (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    (t • (fourGrp x₁ x₂ : Set G)).ncard = 4 ∧
    (t • (fourGrp x₁ x₂ : Set G) ∪ tau • (fourGrp x₁ x₂ : Set G)).ncard = 8 ∧
    (t • (fourGrp x₁ x₂ : Set G) ∪ (t * tau) • (fourGrp x₁ x₂ : Set G)).ncard = 8 := by
  have hFL : fourGrp x₁ x₂ ≤ L := by
    rw [fourGrp]
    refine (Subgroup.closure_le L).mpr ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (y_z_mem_L h.toCtx0).1
    · exact (y_z_mem_L h.toCtx0).2
  have hFcard : (fourGrp x₁ x₂ : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    exact (h.wreath.fourGrp_eq_omega).2.2
  have hsz : ∀ a : G, (a • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
    intro a
    rw [Set.ncard_smul_set, hFcard]
  have hdisj1 : Disjoint (t • (fourGrp x₁ x₂ : Set G))
      (tau • (fourGrp x₁ x₂ : Set G)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_smul_set] at hx1 hx2
    obtain ⟨f₁, hf₁, h1⟩ := hx1
    obtain ⟨f₂, hf₂, h2⟩ := hx2
    have hmul : t * f₁ = tau * f₂ := by
      rw [← smul_eq_mul, ← smul_eq_mul]
      exact h1.trans h2.symm
    have htau : tau = t * (f₁ * f₂⁻¹) := by
      calc tau = tau * f₂ * f₂⁻¹ := by group
        _ = t * f₁ * f₂⁻¹ := by rw [← hmul]
        _ = t * (f₁ * f₂⁻¹) := by group
    have hf : f₁ * f₂⁻¹ ∈ fourGrp x₁ x₂ :=
      Subgroup.mul_mem _ hf₁ (Subgroup.inv_mem _ hf₂)
    exact h.tau_not_mem (htau.symm ▸ Subgroup.mul_mem _
      (Subgroup.mem_sup_left h.hyp.mem_twoCore) (Subgroup.mem_sup_right (hFL hf)))
  have hdisj2 : Disjoint (t • (fourGrp x₁ x₂ : Set G))
      ((t * tau) • (fourGrp x₁ x₂ : Set G)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_smul_set] at hx1 hx2
    obtain ⟨f₁, hf₁, h1⟩ := hx1
    obtain ⟨f₂, hf₂, h2⟩ := hx2
    have hmul : t * f₁ = (t * tau) * f₂ := by
      rw [← smul_eq_mul, ← smul_eq_mul]
      exact h1.trans h2.symm
    have hft : f₁ = tau * f₂ := by
      apply mul_left_cancel (a := t)
      rw [hmul]; group
    have htau : tau = f₁ * f₂⁻¹ := by
      rw [hft]; group
    have hf : f₁ * f₂⁻¹ ∈ fourGrp x₁ x₂ :=
      Subgroup.mul_mem _ hf₁ (Subgroup.inv_mem _ hf₂)
    exact h.tau_not_mem (htau.symm ▸ Subgroup.mem_sup_right (hFL hf))
  refine ⟨hsz t, ?_, ?_⟩
  · rw [Set.ncard_union_eq hdisj1, hsz t, hsz tau]
  · rw [Set.ncard_union_eq hdisj2, hsz t, hsz (t * tau)]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
