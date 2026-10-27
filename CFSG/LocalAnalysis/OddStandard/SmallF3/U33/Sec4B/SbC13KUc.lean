module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KU0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma c13K_inv_eq_self_of_sq {a : G} (h : a ^ 2 = 1) : a⁻¹ = a := by
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h

private lemma c13K_fourGrp_le_baseGrp (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  change closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) ≤ baseGrp x₁ x₂
  refine (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact (baseGrp x₁ x₂).pow_mem (Subgroup.subset_closure (by simp)) 2
  · have hx1 : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hx2 : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    exact (baseGrp x₁ x₂).pow_mem (mul_mem hx1 hx2) 2

theorem c13K_U_comm_le (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    ⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ ≤
      ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G) := by
  let U : Subgroup G := ctxU t tau x₁ x₂ lam
  let B : Subgroup G := ctxQ t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)
  change ⁅U, U⁆ ≤ B
  have hBU : B ≤ U := (c13K_Q_B_le_O hc).2.trans le_sup_left
  let B0 : Subgroup ↥U := B.subgroupOf U
  haveI hB0norm : B0.Normal := by
    refine (Subgroup.normal_subgroupOf_iff (H := B) (K := U) hBU).mpr ?_
    intro h k hh hk
    exact c13K_B_normal_U hc k hk h hh
  have hcard : Nat.card (↥U ⧸ B0) = 2 ^ 2 := by
    rw [← Subgroup.index_eq_card]
    show B.relIndex U = 2 ^ 2
    have h := Subgroup.relIndex_mul_card (H := B) (K := U)
    rw [inf_eq_left.mpr hBU, c13K_card_B hc, c13K_card_U hc] at h
    omega
  haveI : IsMulCommutative (↥U ⧸ B0) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
  have hcomm : _root_.commutator ↥U ≤ B0 :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := B0)).mp inferInstance
  calc ⁅U, U⁆ = (_root_.commutator ↥U).map U.subtype :=
        (Subgroup.map_subtype_commutator U).symm
    _ ≤ B0.map U.subtype := Subgroup.map_mono hcomm
    _ = B := Subgroup.map_subgroupOf_eq_of_le hBU

theorem c13K_U_comm_ge (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    tau ∈ ⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ ∧
      x₁ * x₂ ∈ ⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ ∧
      ctxYq t tau x₁ x₂ rho ≤ ⁅ctxU t tau x₁ x₂ lam, ctxU t tau x₁ x₂ lam⁆ := by
  let U : Subgroup G := ctxU t tau x₁ x₂ lam
  let U' : Subgroup G := ⁅U, U⁆
  change tau ∈ U' ∧ x₁ * x₂ ∈ U' ∧ ctxYq t tau x₁ x₂ rho ≤ U'
  obtain ⟨V', v₁, v₂, hV⟩ := hc.data_V
  obtain ⟨_, _, hQsplit, _, _, _, hYsplit, _, hv1_mem, _, ht_v1, hv2_mem, _, hVclos,
    ht_v2, hlamt_v2, _, hw1, _⟩ := hV
  have hQU : ctxQ t tau x₁ x₂ rho ≤ U := (c13K_Q_B_le_O hc).1.trans le_sup_left
  have hV'Q : V' ≤ ctxQ t tau x₁ x₂ rho :=
    hQsplit ▸ (le_sup_right : V' ≤ baseGrp x₁ x₂ ⊔ V')
  have hV'U : V' ≤ U := hV'Q.trans hQU
  have hfourQ : fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho :=
    (c13K_fourGrp_le_baseGrp x₁ x₂).trans hc.base_le_Q
  have htU : t ∈ U :=
    Subgroup.mem_sup_left (hc.R_le_O (hc.X_le_R (Subgroup.subset_closure (by simp))))
  have hlamU : lam ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  have homU : om ∈ U := Subgroup.mem_sup_left (Subgroup.mem_inf.mp hc.om_mem).1
  have hx1Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx2Q : x₂ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx1U : x₁ ∈ U := hQU hx1Q
  have hx1sqQ : x₁ ^ 2 ∈ ctxQ t tau x₁ x₂ rho :=
    (ctxQ t tau x₁ x₂ rho).pow_mem hx1Q 2
  have hzQ : (x₁ * x₂) ^ 2 ∈ ctxQ t tau x₁ x₂ rho :=
    (ctxQ t tau x₁ x₂ rho).pow_mem ((ctxQ t tau x₁ x₂ rho).mul_mem hx1Q hx2Q) 2
  have hv1Q : v₁ ∈ ctxQ t tau x₁ x₂ rho := hV'Q hv1_mem
  have hv2Q : v₂ ∈ ctxQ t tau x₁ x₂ rho := hV'Q hv2_mem
  have hv1U : v₁ ∈ U := hV'U hv1_mem
  have hv2U : v₂ ∈ U := hV'U hv2_mem
  have hlamtU : lam * t ∈ U := U.mul_mem hlamU htU
  have htinv : t⁻¹ = t := c13K_inv_eq_self_of_sq (c13K_rel hc).1
  have hominv : om⁻¹ = om := c13K_inv_eq_self_of_sq (c13K_rel hc).2.2.1
  have ht2 : t * t = 1 := by simpa [pow_two] using (c13K_rel hc).1
  have hom2 : om * om = 1 := by simpa [pow_two] using (c13K_rel hc).2.2.1
  have htom : ⁅t, om⁆ = tau := by
    rw [commutatorElement_def]
    have homt : om * t = t * tau * om := by
      calc om * t = om * t * om⁻¹ * om := by group
        _ = (t * tau) * om := by rw [hc.t_om]
    calc t * om * t⁻¹ * om⁻¹ = t * (om * t) * om := by
          rw [htinv, hominv]; group
      _ = t * (t * tau * om) * om := by rw [homt]
      _ = tau := by
          rw [show t * (t * tau * om) * om = (t * t) * tau * (om * om) by group,
            ht2, hom2]
          group
  have htauU' : tau ∈ U' := htom ▸ Subgroup.commutator_mem_commutator htU homU
  have hyU' : x₁ ^ 2 ∈ U' := by
    have hcomm : ⁅t, v₂⁆ = x₁ ^ 2 := by
      rw [commutatorElement_def, ht_v2]
      calc (v₂ * x₁ ^ 2) * v₂⁻¹ = (x₁ ^ 2 * v₂) * v₂⁻¹ := by
            rw [hc.Q_comm v₂ hv2Q (x₁ ^ 2) hx1sqQ]
        _ = x₁ ^ 2 := by group
    exact hcomm ▸ Subgroup.commutator_mem_commutator htU hv2U
  have hzU' : (x₁ * x₂) ^ 2 ∈ U' := by
    have hcomm : ⁅t, v₁⁆ = (x₁ * x₂) ^ 2 := by
      rw [commutatorElement_def, ht_v1]
      calc (v₁ * (x₁ * x₂) ^ 2) * v₁⁻¹ = ((x₁ * x₂) ^ 2 * v₁) * v₁⁻¹ := by
            rw [hc.Q_comm v₁ hv1Q ((x₁ * x₂) ^ 2) hzQ]
        _ = (x₁ * x₂) ^ 2 := by group
    exact hcomm ▸ Subgroup.commutator_mem_commutator htU hv1U
  have hFour_le : fourGrp x₁ x₂ ≤ U' := by
    change closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) ≤ U'
    refine (Subgroup.closure_le (K := U')).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hyU'
    · exact hzU'
  have hv1U' : v₁ ∈ U' := by
    have hcomm : ⁅lam * t, v₂⁆ = v₁ := by
      rw [commutatorElement_def, hlamt_v2]
      calc (v₂ * v₁) * v₂⁻¹ = (v₁ * v₂) * v₂⁻¹ := by
            rw [hc.Q_comm v₂ hv2Q v₁ hv1Q]
        _ = v₁ := by group
    exact hcomm ▸ Subgroup.commutator_mem_commutator hlamtU hv2U
  have hv2U' : v₂ ∈ U' := by
    obtain ⟨w, hwV, hw_eq⟩ := hw1
    have hwQ : w ∈ ctxQ t tau x₁ x₂ rho := hfourQ hwV
    have hcomm : ⁅om, x₁⁆ = v₂ * w := by
      rw [commutatorElement_def, hw_eq]
      calc (x₁ * v₂ * w) * x₁⁻¹ = (v₂ * x₁ * w) * x₁⁻¹ := by
            rw [hc.Q_comm x₁ hx1Q v₂ hv2Q]
        _ = v₂ * (x₁ * w) * x₁⁻¹ := by group
        _ = v₂ * (w * x₁) * x₁⁻¹ := by rw [hc.Q_comm x₁ hx1Q w hwQ]
        _ = v₂ * w := by group
    have hvw : v₂ * w ∈ U' := hcomm ▸ Subgroup.commutator_mem_commutator homU hx1U
    have hwU' : w ∈ U' := hFour_le hwV
    have hvw_eq : v₂ = (v₂ * w) * w⁻¹ := by group
    rw [hvw_eq]
    exact U'.mul_mem hvw (U'.inv_mem hwU')
  have hVprime_le : V' ≤ U' := by
    rw [hVclos]
    refine (Subgroup.closure_le (K := U')).mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hv1U'
    · exact hv2U'
  have hx1x2U' : x₁ * x₂ ∈ U' := by
    have hcomm : ⁅lam, x₁⁆ = x₂ * x₁⁻¹ := by
      rw [commutatorElement_def, hc.wreath.conj_x₁]
    have hmem : x₂ * x₁⁻¹ ∈ U' := hcomm ▸ Subgroup.commutator_mem_commutator hlamU hx1U
    have hyU'2 : x₁ ^ 2 ∈ U' := hFour_le (Subgroup.subset_closure (by simp))
    have heq : x₁ * x₂ = (x₂ * x₁⁻¹) * x₁ ^ 2 := by
      rw [pow_two]
      calc x₁ * x₂ = x₂ * x₁ := hc.wreath.comm
        _ = x₂ * x₁⁻¹ * (x₁ * x₁) := by group
    rw [heq]
    exact U'.mul_mem hmem hyU'2
  refine ⟨htauU', hx1x2U', ?_⟩
  rw [hYsplit]
  exact sup_le hFour_le hVprime_le

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
