module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma R_le_M (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
  refine hc.R_le_O.trans ?_
  rw [ctxO]
  exact Subgroup.map_subtype_le _

private lemma R_comm_fourGrp (hc : Ctx11 t L S x₁ x₂ lam rho tau) {a v : G}
    (ha : a ∈ ctxR t tau x₁ x₂) (hv : v ∈ fourGrp x₁ x₂) : a * v = v * a := by
  have hvCent : v ∈ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    have hmem : v ∈ ctxO t tau x₁ x₂ ⊓
        centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
      rw [hc.center_O]; exact hv
    exact hmem.2
  have haO : a ∈ ctxO t tau x₁ x₂ := hc.R_le_O ha
  exact Subgroup.mem_centralizer_iff.mp hvCent a haO

private lemma sq_centralizes_base (hc : Ctx11 t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxR t tau x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) :
    a ^ 2 * b = b * a ^ 2 := by
  let v : G := a * b * a⁻¹ * b⁻¹
  have hv : v ∈ fourGrp x₁ x₂ := l12_comm_B_mem_V hc ha hb
  have hcomm_av : a * v = v * a := R_comm_fourGrp hc ha hv
  have hv2 : v * v = 1 := by
    have h := (hc.wreath.fourGrp_eq_omega).2.1.2 v hv
    simpa [pow_two] using h
  have hba : a * b * a⁻¹ = v * b := by
    dsimp [v]; group
  have hcalc : (a * a) * b * (a * a)⁻¹ = b := by
    calc
      (a * a) * b * (a * a)⁻¹ = a * (a * b * a⁻¹) * a⁻¹ := by group
      _ = a * (v * b) * a⁻¹ := by rw [hba]
      _ = v * (a * b * a⁻¹) := by
        calc
          a * (v * b) * a⁻¹ = (a * v) * b * a⁻¹ := by group
          _ = (v * a) * b * a⁻¹ := by rw [hcomm_av]
          _ = v * (a * b * a⁻¹) := by group
      _ = v * (v * b) := by rw [hba]
      _ = b := by rw [← mul_assoc, hv2, one_mul]
  have h2 : (a * a) * b = b * (a * a) := by
    calc
      (a * a) * b = ((a * a) * b * (a * a)⁻¹) * (a * a) := by group
      _ = b * (a * a) := by rw [hcalc]
  simpa [pow_two] using h2

theorem l12_sq_mem_V (hc : Ctx11 t L S x₁ x₂ lam rho tau) {a : G} (ha : a ∈ ctxR t tau x₁ x₂) :
    a ^ 2 ∈ fourGrp x₁ x₂ := by
  have hN : a ^ 2 ∈ ctxN tau x₁ x₂ := l12_sq_mem_N hc ha
  rcases l12_N_cases hc.toCtx4 hN with hV | htauV
  · exact hV
  · exfalso
    have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hx₁R : x₁ ∈ ctxR t tau x₁ x₂ := by
      rw [hc.R_eq]
      exact Subgroup.mem_sup_left (hc.base_le_Q hx₁B)
    have hcomm1 : (tau * a ^ 2) * x₁ = x₁ * (tau * a ^ 2) := by
      have hx₁O : x₁ ∈ ctxO t tau x₁ x₂ := hc.R_le_O hx₁R
      have hvCent : tau * a ^ 2 ∈
          centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
        have hmem : tau * a ^ 2 ∈ ctxO t tau x₁ x₂ ⊓
            centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
          rw [hc.center_O]; exact htauV
        exact hmem.2
      exact (Subgroup.mem_centralizer_iff.mp hvCent x₁ hx₁O).symm
    have hcomm2 : a ^ 2 * x₁ = x₁ * a ^ 2 := sq_centralizes_base hc ha hx₁B
    have hcomm2i : (a ^ 2)⁻¹ * x₁ = x₁ * (a ^ 2)⁻¹ := by
      calc
        (a ^ 2)⁻¹ * x₁ = (a ^ 2)⁻¹ * (x₁ * a ^ 2) * (a ^ 2)⁻¹ := by group
        _ = (a ^ 2)⁻¹ * ((a ^ 2) * x₁) * (a ^ 2)⁻¹ := by rw [hcomm2]
        _ = x₁ * (a ^ 2)⁻¹ := by group
    have htau_comm : tau * x₁ = x₁ * tau := by
      have htau_eq : tau = (tau * a ^ 2) * (a ^ 2)⁻¹ := by group
      rw [htau_eq]
      calc
        (tau * a ^ 2) * (a ^ 2)⁻¹ * x₁ = (tau * a ^ 2) * ((a ^ 2)⁻¹ * x₁) := by group
        _ = (tau * a ^ 2) * (x₁ * (a ^ 2)⁻¹) := by rw [hcomm2i]
        _ = x₁ * ((tau * a ^ 2) * (a ^ 2)⁻¹) := by
          calc
            (tau * a ^ 2) * (x₁ * (a ^ 2)⁻¹) =
                ((tau * a ^ 2) * x₁) * (a ^ 2)⁻¹ := by group
            _ = (x₁ * (tau * a ^ 2)) * (a ^ 2)⁻¹ := by rw [hcomm1]
            _ = x₁ * ((tau * a ^ 2) * (a ^ 2)⁻¹) := by group
    have hx : x₁⁻¹ = x₁ := by
      rw [← hc.tau_x₁, htau_comm]
      group
    have hsq : x₁ ^ 2 = 1 := by
      calc
        x₁ ^ 2 = x₁ * x₁ := by rw [pow_two]
        _ = x₁ * x₁⁻¹ := by rw [hx]
        _ = 1 := mul_inv_cancel x₁
    have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h4 : orderOf x₁ = 4 := hc.wreath.ord_x₁
    rw [h4] at hdvd
    norm_num at hdvd

theorem l12_comm_mem_V (hc : Ctx11 t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ ctxR t tau x₁ x₂) (hb : b ∈ ctxR t tau x₁ x₂) :
    a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := by
  have hab : a * b ∈ ctxR t tau x₁ x₂ := Subgroup.mul_mem _ ha hb
  have hsab : (a * b) ^ 2 ∈ fourGrp x₁ x₂ := l12_sq_mem_V hc hab
  have hsb : b ^ 2 ∈ fourGrp x₁ x₂ := l12_sq_mem_V hc hb
  have hsa : a ^ 2 ∈ fourGrp x₁ x₂ := l12_sq_mem_V hc ha
  have hsa' : a⁻¹ * a⁻¹ ∈ fourGrp x₁ x₂ := by
    rw [← mul_inv_rev, ← pow_two]
    exact Subgroup.inv_mem _ hsa
  have hsb' : b⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := by
    rw [← mul_inv_rev, ← pow_two]
    exact Subgroup.inv_mem _ hsb
  have hconj : b⁻¹ * (a⁻¹ * a⁻¹) * b ∈ fourGrp x₁ x₂ := by
    have hbM : b⁻¹ ∈ ctxM t tau x₁ x₂ := R_le_M hc (Subgroup.inv_mem _ hb)
    have h := hc.normal_V.2 b⁻¹ hbM (a⁻¹ * a⁻¹) hsa'
    simpa using h
  have hprod : (a * b) ^ 2 * (b⁻¹ * (a⁻¹ * a⁻¹) * b) * (b⁻¹ * b⁻¹) ∈ fourGrp x₁ x₂ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hsab hconj) hsb'
  have hid : a * b * a⁻¹ * b⁻¹ =
      (a * b) ^ 2 * (b⁻¹ * (a⁻¹ * a⁻¹) * b) * (b⁻¹ * b⁻¹) := by
    simp [pow_two, mul_assoc]
  rw [hid]
  exact hprod

theorem l12_phi_R (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxPhi (ctxR t tau x₁ x₂) = fourGrp x₁ x₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥(ctxR t tau x₁ x₂)) := ⟨l12_isPGroup_R hc⟩
  have hle : ctxPhi (ctxR t tau x₁ x₂) ≤ fourGrp x₁ x₂ := by
    rw [ctxPhi]
    refine Subgroup.map_le_iff_le_comap.mpr ?_
    rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le (K := Subgroup.comap (ctxR t tau x₁ x₂).subtype
      (fourGrp x₁ x₂))).2 ?_
    intro z hz
    rcases hz with hz | hz
    · rw [commutator_eq_closure] at hz
      refine (Subgroup.closure_le (K := Subgroup.comap (ctxR t tau x₁ x₂).subtype
      (fourGrp x₁ x₂))).2 ?_ hz
      intro w hw
      rw [mem_commutatorSet_iff] at hw
      obtain ⟨u, v, rfl⟩ := hw
      exact l12_comm_mem_V hc u.2 v.2
    · obtain ⟨x, rfl⟩ := hz
      exact l12_sq_mem_V hc x.2
  have hge : fourGrp x₁ x₂ ≤ ctxPhi (ctxR t tau x₁ x₂) := by
    have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hx₁R : x₁ ∈ ctxR t tau x₁ x₂ := by
      rw [hc.R_eq]; exact Subgroup.mem_sup_left (hc.base_le_Q hx₁B)
    have hx₂R : x₂ ∈ ctxR t tau x₁ x₂ := by
      rw [hc.R_eq]; exact Subgroup.mem_sup_left (hc.base_le_Q hx₂B)
    have hprodR : x₁ * x₂ ∈ ctxR t tau x₁ x₂ := Subgroup.mul_mem _ hx₁R hx₂R
    rw [fourGrp, Subgroup.closure_le]
    intro y hy
    rcases (by simpa using hy) with rfl | rfl
    · rw [ctxPhi]
      exact Subgroup.mem_map.mpr
        ⟨(⟨x₁, hx₁R⟩ : ↥(ctxR t tau x₁ x₂)) ^ 2,
          pth_power_mem_frattini_of_isPGroup (p := 2) _, by simp⟩
    · rw [ctxPhi]
      exact Subgroup.mem_map.mpr
        ⟨(⟨x₁ * x₂, hprodR⟩ : ↥(ctxR t tau x₁ x₂)) ^ 2,
          pth_power_mem_frattini_of_isPGroup (p := 2) _, by simp⟩
  exact le_antisymm hle hge

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
