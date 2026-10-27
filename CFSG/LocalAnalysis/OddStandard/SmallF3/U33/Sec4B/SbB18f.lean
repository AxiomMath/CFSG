module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18n

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma l18_conj_mem_smulY (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {m w : G}
    (hm : m ∈ ctxXi t tau x₁ x₂ rho) (hwC : w ∈ ctxCY t tau x₁ x₂ rho)
    (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hInv : InvIn (w • (ctxQ t tau x₁ x₂ rho : Set G)) =
      w • (ctxYq t tau x₁ x₂ rho : Set G)) :
    m * w * m⁻¹ ∈ w • (ctxYq t tau x₁ x₂ rho : Set G) := by
  have hmC : m ∈ ctxCY t tau x₁ x₂ rho := l18_Xi_le_C hc hm
  have hcomm : m * w * m⁻¹ * w⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    l18_comm_mem_Q hc.toCtx18 hmC hwC
  have hwK : w ∈ ctxK t tau x₁ x₂ rho := hwC.1
  have huQ : m * w * m⁻¹ ∈ w • (ctxQ t tau x₁ x₂ rho : Set G) := by
    refine Set.mem_smul_set.mpr ⟨w⁻¹ * (m * w * m⁻¹ * w⁻¹) * w, ?_, ?_⟩
    · have h := hc.normal_Q_K.2 w⁻¹ (Subgroup.inv_mem _ hwK) _ hcomm
      simpa using h
    · change w * (w⁻¹ * (m * w * m⁻¹ * w⁻¹) * w) = m * w * m⁻¹
      group
  have hu2 : (m * w * m⁻¹) ^ 2 = 1 := by
    have hw : m * w * m⁻¹ = (MulAut.conj m) w := by rw [MulAut.conj_apply]
    rw [hw, ← map_pow, hw2, map_one]
  have hu1 : m * w * m⁻¹ ≠ 1 := by
    intro h
    exact hw1 (by
      calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
        _ = m⁻¹ * 1 * m := by rw [h]
        _ = 1 := by group)
  have hu : m * w * m⁻¹ ∈ InvIn (w • (ctxQ t tau x₁ x₂ rho : Set G)) := ⟨huQ, hu2, hu1⟩
  rwa [hInv] at hu

theorem l18_comm_om_mem_Y (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {m : G}
    (hm : m ∈ ctxXi t tau x₁ x₂ rho) : m * om * m⁻¹ * om⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  have homC : om ∈ ctxCY t tau x₁ x₂ rho :=
    l18_QA_le_C hc.toCtx13 (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hom1 : om ≠ 1 := by
    intro h
    exact hc.om_not_mem (by rw [h]; exact Subgroup.one_mem _)
  have hmem := l18_conj_mem_smulY hc hm homC hc.om_sq hom1 hc.Q_om.2.2.2.2
  obtain ⟨y, hy, hyu⟩ := Set.mem_smul_set.mp hmem
  have hEq : m * om * m⁻¹ * om⁻¹ = y := by
    rw [← hyu]
    change (om * y) * om⁻¹ = y
    rw [hc.om_cent_Y y hy]
    group
  rw [hEq]
  exact hy

theorem l18_comm_tau_mem_Y (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {m : G}
    (hm : m ∈ ctxXi t tau x₁ x₂ rho) : m * tau * m⁻¹ * tau⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  have hrel := ctx13_relations hc.toCtx13
  have ht2 : t ^ 2 = 1 := hrel.1
  have htau2 : tau ^ 2 = 1 := hrel.2.2.2.1
  have hcomm_tt : t * tau = tau * t := hrel.2.2.2.2.2.1
  have homC : om ∈ ctxCY t tau x₁ x₂ rho :=
    l18_QA_le_C hc.toCtx13 (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have hwC : om * tau ∈ ctxCY t tau x₁ x₂ rho := by
    refine l18_QA_le_C hc.toCtx13 (Subgroup.mem_sup_right ?_)
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hom1 : om ≠ 1 := by
    intro h
    exact hc.om_not_mem (by rw [h]; exact Subgroup.one_mem _)
  have hw1 : om * tau ≠ 1 := by
    intro h
    exact Ctx13.omtau_not_mem_Q hc.toCtx13 (by rw [h]; exact Subgroup.one_mem _)
  have hom_tau : om * tau = tau * om := om_tau_comm ht2 hc.om_sq htau2 hcomm_tt hc.t_om
  have hw2 : (om * tau) ^ 2 = 1 := by
    have hComm : Commute om tau := hom_tau
    rw [hComm.mul_pow, hc.om_sq, htau2, mul_one]
  have homMem := l18_conj_mem_smulY hc hm homC hc.om_sq hom1 hc.Q_om.2.2.2.2
  obtain ⟨y, hy, hyu⟩ := Set.mem_smul_set.mp homMem
  have hwMem := l18_conj_mem_smulY hc hm hwC hw2 hw1 hc.Q_omtau.2.2.2.2
  obtain ⟨y', hy', hy'u'⟩ := Set.mem_smul_set.mp hwMem
  have hz : y⁻¹ * y' ∈ ctxYq t tau x₁ x₂ rho :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hy'
  have homeq : om⁻¹ = om :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hc.om_sq)
  have htaueq : tau⁻¹ = tau :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact htau2)
  have h_om_y : om * y = y * om := hc.om_cent_Y y hy
  have h_tau_y : tau * y = y * tau := hc.tau_cent_Y y hy
  have h_inv_y : y⁻¹ * om = om * y⁻¹ := by
    have := congrArg Inv.inv h_om_y
    simpa [mul_inv_rev, homeq] using this
  have h_inv_tau : y⁻¹ * tau = tau * y⁻¹ := by
    have := congrArg Inv.inv h_tau_y
    simpa [mul_inv_rev, htaueq] using this
  have hmt : m * tau * m⁻¹ = tau * (y⁻¹ * y') := by
    have h1 : m * tau * m⁻¹ = (m * om * m⁻¹)⁻¹ * (m * (om * tau) * m⁻¹) := by group
    rw [h1, ← hyu, ← hy'u']
    change (om * y)⁻¹ * ((om * tau) * y') = tau * (y⁻¹ * y')
    have hom_yy : (om * y)⁻¹ = om * y⁻¹ := by
      rw [mul_inv_rev, homeq, h_inv_y]
    rw [hom_yy]
    calc (om * y⁻¹) * ((om * tau) * y')
        = y⁻¹ * (om * om) * tau * y' := by rw [← h_inv_y]; group
      _ = y⁻¹ * tau * y' := by rw [← pow_two, hc.om_sq]; group
      _ = tau * (y⁻¹ * y') := by rw [h_inv_tau]; group
  have hgoal : m * tau * m⁻¹ * tau⁻¹ = y⁻¹ * y' := by
    rw [hmt, hc.tau_cent_Y (y⁻¹ * y') hz]
    group
  rw [hgoal]
  exact hz

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
