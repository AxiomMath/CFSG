module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_lam_y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  rw [← conj_pow (a := lam) (b := x₁) (i := 2), hc.wreath.conj_x₁, hc.wreath.x₂_sq]

theorem l17_lam_z (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
  have hlam2 : lam * lam = 1 := by
    have h := pow_orderOf_eq_one lam
    rw [hc.wreath.ord_lam] at h
    simpa [pow_two] using h
  have hx₂ : lam * x₂ * lam⁻¹ = x₁ := by
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [hc.wreath.conj_x₁]
      _ = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by simp only [mul_assoc]
      _ = x₁ := by
        have hli : lam⁻¹ * lam⁻¹ = 1 := by rw [← mul_inv_rev, hlam2, inv_one]
        rw [hlam2, hli, one_mul, mul_one]
  have hz : lam * (x₁ * x₂) * lam⁻¹ = x₁ * x₂ := by
    calc lam * (x₁ * x₂) * lam⁻¹
        = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) :=
          (conj_mul (b := lam) (a := x₁) (c := x₂)).symm
      _ = x₂ * x₁ := by rw [hc.wreath.conj_x₁, hx₂]
      _ = x₁ * x₂ := hc.wreath.comm.symm
  rw [← conj_pow (a := lam) (b := x₁ * x₂) (i := 2), hz]

theorem l17_lam_comm (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    lam * t = t * lam ∧ lam * tau = tau * lam ∧ lam * om = om * lam := by
  have hlamL : lam ∈ L := (S4A.generators_mem_L hc.toCtx0).2.2
  have hlamH : lam ∈ invCent t := S4A.L_le_invCent hc.hyp hlamL
  have ht : lam * t = t * lam := S4A.mem_invCent_iff.mp hlamH
  have hom : lam * om = om * lam := by
    calc lam * om = (lam * om * lam⁻¹) * lam := by
          simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = om * lam := by rw [hc.lam_om]
  exact ⟨ht, hc.tau_lam.symm, hom⟩

theorem l17_cent_V (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ v ∈ fourGrp x₁ x₂, t * v = v * t ∧ tau * v = v * tau ∧ om * v = v * om := by
  have hy : x₁ ^ 2 ∈ invCent t :=
    S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).1
  have hz : (x₁ * x₂) ^ 2 ∈ invCent t :=
    S4A.L_le_invCent hc.hyp (S4A.y_z_mem_L hc.toCtx0).2
  have hV : fourGrp x₁ x₂ ≤ invCent t := by
    rw [fourGrp, Subgroup.closure_le]
    rintro g (hg : g ∈ ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
    rcases hg with rfl | rfl
    · exact hy
    · exact hz
  have hVY : fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho := by
    rw [← hc.Y_cent.1]
    exact inf_le_left
  intro v hv
  have htv : t * v = v * t := (S4A.mem_invCent_iff.mp (hV hv)).symm
  have hvY : v ∈ ctxYq t tau x₁ x₂ rho := hVY hv
  exact ⟨htv, hc.tau_cent_Y v hvY, hc.om_cent_Y v hvY⟩

theorem l17_V_elem (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (fourGrp x₁ x₂) :=
  (WreathRel.fourGrp_eq_omega hc.wreath).2.1

theorem l17_yz_ne (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    x₁ ^ 2 ≠ 1 ∧ (x₁ * x₂) ^ 2 ≠ 1 ∧ x₁ ^ 2 ≠ (x₁ * x₂) ^ 2 := by
  refine ⟨?_, hc.wreath.sq_x₁x₂_ne_one, ?_⟩
  · intro h
    have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hc.wreath.ord_x₁] at hdvd
    norm_num at hdvd
  · intro h
    have hx₂sq : x₂ ^ 2 = 1 := by
      rw [hc.wreath.x₂_sq, h]
      exact hc.wreath.sq_x₁x₂_mul_self
    have hdvd : orderOf x₂ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx₂sq
    rw [hc.wreath.ord_x₂] at hdvd
    norm_num at hdvd

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
