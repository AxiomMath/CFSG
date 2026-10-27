module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusFour
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusHom

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 Certificates.FzJ36 Certificates.FzFus

variable {G : Type} [Group G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G} {π : Model →* G}

section

variable (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π)
include hd

theorem FzfDict.z1M_eq : π z1M = x₁ ^ 2 := by
  rw [(hd.eq_iff z1M (x1M * x1M)).mpr z1M_keq, map_mul, hd.x₁_eq, pow_two]

theorem FzfDict.z2M_eq : π z2M = x₂ ^ 2 := by
  rw [(hd.eq_iff z2M (x2M * x2M)).mpr z2M_keq, map_mul, hd.x₂_eq, pow_two]

theorem FzfDict.z3M_eq : π z3M = (x₁ * x₂) ^ 2 := by
  rw [(hd.eq_iff z3M (x1M * x2M * (x1M * x2M))).mpr z3M_keq]
  simp only [map_mul, hd.x₁_eq, hd.x₂_eq, pow_two]

end

private theorem x1sq_mem : x₁ ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)

private theorem z3_mem : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := subset_closure (by simp)

private theorem x2sq_mem (h12 : x₁ * x₂ = x₂ * x₁) : x₂ ^ 2 ∈ fourGrp x₁ x₂ := by
  have : x₂ ^ 2 = (x₁ ^ 2)⁻¹ * (x₁ * x₂) ^ 2 := by
    rw [Commute.mul_pow h12 2]
    group
  rw [this]
  exact mul_mem (inv_mem x1sq_mem) z3_mem

theorem fzfus_letters (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) (h12 : x₁ * x₂ = x₂ * x₁)
    {n : N3} (hi2 : π ⟨n, 1⟩ ^ 2 = 1) (hiZ : π ⟨n, 1⟩ ∉ fourGrp x₁ x₂) :
    IsInvM ⟨n, 1⟩ ∧ (lett n.1 ≠ 0 ∧ lett n.2.1 ≠ 0 ∧ lett n.2.2 ≠ 0) := by
  have h1 : π ⟨n, 1⟩ ≠ 1 := fun h1 => hiZ (h1 ▸ Subgroup.one_mem _)
  have hinv : IsInvM ⟨n, 1⟩ := (hd.isInvM_iff _).mpr ⟨by rw [← pow_two]; exact hi2, h1⟩
  refine ⟨hinv, ?_⟩
  by_contra hnot
  rcases central_of_inv n hinv hnot with hk | hk | hk
  · exact hiZ (by rw [(hd.eq_iff _ _).mpr hk, hd.z1M_eq]; exact x1sq_mem)
  · exact hiZ (by rw [(hd.eq_iff _ _).mpr hk, hd.z2M_eq]; exact x2sq_mem h12)
  · exact hiZ (by rw [(hd.eq_iff _ _).mpr hk, hd.z3M_eq]; exact z3_mem)

theorem fzfus_rep_not_four (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π)
    (h12 : x₁ * x₂ = x₂ * x₁) {c : Cls} (hc : c ∈ rzList) :
    π (rep c) ∉ fourGrp x₁ x₂ := by
  obtain ⟨hinv, hz1, hz3, hz13, -⟩ := rz_rep_facts c hc
  obtain ⟨-, hZ1, hZ3, -⟩ := label_facts
  have ha : x₁ ^ 2 * x₁ ^ 2 = 1 := by
    have := ((hd.isInvM_iff z1M).mp hZ1).1
    rwa [hd.z1M_eq] at this
  have hb : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
    have := ((hd.isInvM_iff z3M).mp hZ3).1
    rwa [hd.z3M_eq] at this
  have hab : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 :=
    ((Commute.refl x₁).mul_right h12).pow_pow 2 2
  intro hmem
  rcases fzfus_mem_four ha hb hab hmem with h | h | h | h
  · exact ((hd.isInvM_iff _).mp hinv).2 h
  · exact hz1 ((hd.eq_iff _ _).mp (h.trans hd.z1M_eq.symm))
  · exact hz3 ((hd.eq_iff _ _).mp (h.trans hd.z3M_eq.symm))
  · refine hz13 ((hd.eq_iff _ _).mp ?_)
    rw [h, map_mul, hd.z1M_eq, hd.z3M_eq]

