module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4T2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Frame

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem y4c_phi_inv {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {y : G} (hy : y ∈ f3Y s) : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
  have h := f3_phi_mul hH y hy y⁻¹ (inv_mem hy)
  rw [mul_inv_cancel, show f3phi s (1 : G) = 1 by simp [f3phi]] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem y4_exists_c_sq (c : Ctx4 s e) :
    ∃ y ∈ s.C₂, f3phi s y ≠ 1 ∧ y ^ 2 ∈ s.fr.B := by
  have hH : F33Hyp s e := c.toF33
  obtain ⟨y₀, hy₀C, hwV, hw1, hwz⟩ := y4_exists_psi c
  have hy₀Y : y₀ ∈ f3Y s := f3_C₂_le_Y hH hy₀C
  have hphi₀ : f3phi s y₀ = ⁅y₀, s.t⁆ := by rw [commutatorElement_def]
  have hwV' : f3phi s y₀ ∈ cen s.fr.B := hphi₀ ▸ hwV
  have hw1' : f3phi s y₀ ≠ 1 := by rw [hphi₀]; exact hw1
  have hwz' : f3phi s y₀ ≠ s.fr.z := by rw [hphi₀]; exact hwz
  let a : G := y5a s
  have haS : a ∈ s.fr.S := y5a_mem_S s
  have haL : a ∈ L := s3_S_le_L s haS
  have hat : a * s.t = s.t * a := Subgroup.mem_centralizer_iff.mp s.t_mem a haL
  have haX : a ∈ s.X := f3_T_le_X hH (s3_S_le_T s haS)
  have haa : a * a = 1 := by rw [← pow_two]; exact y5a_sq hH
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hww : f3phi s y₀ * f3phi s y₀ = 1 := by
    rw [← pow_two]; exact y4_V_sq c hwV'
  have hz2 : s.fr.z * s.fr.z = 1 := by rw [← pow_two]; exact y4_z_sq c
  set q : G := a * y₀ * a⁻¹ with hq
  have hqC : q ∈ s.C₂ := by rw [hq]; exact f3_C₂_normal hH a haX y₀ hy₀C
  have hqY : q ∈ f3Y s := f3_C₂_le_Y hH hqC
  have hq' : q = a * y₀ * a := by rw [hq, hainv]
  have hq_inv : q⁻¹ = a * y₀⁻¹ * a := by
    rw [hq']
    simp only [mul_inv_rev, inv_inv, hainv]
    group
  have hphiq : f3phi s q = s.fr.z * f3phi s y₀ := by
    have hconj : f3phi s q = a * f3phi s y₀ * a⁻¹ := by
      rw [hq]
      exact f3_phi_conj s hat y₀
    rw [hconj]
    exact y5a_conj_V hH (f3phi s y₀) hwV' hw1' hwz'
  set c₀ : G := y₀ * q⁻¹ with hc0
  have hc₀C : c₀ ∈ s.C₂ := by rw [hc0]; exact mul_mem hy₀C (inv_mem hqC)
  have hc₀Y : c₀ ∈ f3Y s := f3_C₂_le_Y hH hc₀C
  have hphic0 : f3phi s c₀ = s.fr.z := by
    have hmul := f3_phi_mul hH y₀ hy₀Y q⁻¹ (inv_mem hqY)
    rw [y4c_phi_inv hH hqY, hphiq] at hmul
    have hwinv : (f3phi s y₀)⁻¹ = f3phi s y₀ := inv_eq_of_mul_eq_one_right hww
    have hzinv : s.fr.z⁻¹ = s.fr.z := inv_eq_of_mul_eq_one_right hz2
    calc f3phi s c₀ = f3phi s (y₀ * q⁻¹) := by rw [hc0]
      _ = f3phi s y₀ * (s.fr.z * f3phi s y₀)⁻¹ := hmul
      _ = f3phi s y₀ * ((f3phi s y₀)⁻¹ * s.fr.z⁻¹) := by rw [mul_inv_rev]
      _ = f3phi s y₀ * (f3phi s y₀ * s.fr.z) := by rw [hwinv, hzinv]
      _ = s.fr.z := by rw [← mul_assoc, hww, one_mul]
  have hc0eq : c₀ = y₀ * a * y₀⁻¹ * a := by
    rw [hc0, hq_inv]
    group
  have h1conj : a * c₀ * a⁻¹ = a * y₀ * a * y₀⁻¹ := by
    rw [hc0eq, hainv]
    simp only [mul_assoc]
    rw [haa, mul_one]
  have h2conj : c₀⁻¹ = a * y₀ * a * y₀⁻¹ := by
    rw [hc0eq]
    simp only [mul_inv_rev, inv_inv, hainv]
    group
  have hconj_inv : a * c₀ * a⁻¹ = c₀⁻¹ := by rw [h1conj, h2conj]
  have hc0inv_conj : a * c₀⁻¹ * a⁻¹ = c₀ := by
    have h := congrArg Inv.inv hconj_inv
    simp only [mul_inv_rev, inv_inv] at h
    rw [← mul_assoc] at h
    exact h
  have hsq_comm : c₀ ^ 2 = ⁅c₀, a⁆ := by
    rw [pow_two, commutatorElement_def]
    have h : c₀ * a * c₀⁻¹ * a⁻¹ = c₀ * c₀ := by
      calc c₀ * a * c₀⁻¹ * a⁻¹ = c₀ * (a * c₀⁻¹ * a⁻¹) := by group
        _ = c₀ * c₀ := by rw [hc0inv_conj]
    rw [h]
  obtain ⟨u, huT1, huY, huconj⟩ := f3_exists_u hH
  have hphiu : f3phi s u = s.fr.z := by
    unfold f3phi
    rw [huconj]
    group
  have hphi_t2 : f3phi s (c₀ * u⁻¹) = 1 := by
    rw [f3_phi_mul hH c₀ hc₀Y u⁻¹ (inv_mem huY), hphic0, y4c_phi_inv hH huY, hphiu]
    exact mul_inv_cancel s.fr.z
  have ht2X0 : c₀ * u⁻¹ ∈ f3X0 s :=
    (f3_phi_eq_one hH (c₀ * u⁻¹) (mul_mem hc₀Y (inv_mem huY))).mp hphi_t2
  have ht2H : c₀ * u⁻¹ ∈ s.H := (Subgroup.mem_inf.mp ht2X0).1
  have ht2comm : (c₀ * u⁻¹) * s.t = s.t * (c₀ * u⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (show c₀ * u⁻¹ ∈ centralizer ({s.t} : Set G) from ht2H)
  have ht2T2 : c₀ * u⁻¹ ∈ s.T₂ :=
    mul_mem (y4_C2_le_T2 s hc₀C) (inv_mem (f3_c8 hH huT1))
  have ht2T : c₀ * u⁻¹ ∈ s.T := y4_T2_comm_t c ht2T2 ht2comm
  have hc0T1 : c₀ ∈ e.T₁ := by
    have h := mul_mem (e.T_le ht2T) huT1
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h
  have hnormal : ∀ hh k, hh ∈ s.fr.S → k ∈ e.T₁ → k * hh * k⁻¹ ∈ s.fr.S :=
    (normal_subgroupOf_iff c.h32.2.1.1).mp c.h32.2.1.2
  have hconj_mem : c₀ * a * c₀⁻¹ ∈ s.fr.S := hnormal a c₀ haS hc0T1
  have hc0sq_S : c₀ ^ 2 ∈ s.fr.S := by
    rw [hsq_comm, commutatorElement_def]
    exact mul_mem hconj_mem (inv_mem haS)
  have hc0sq_C : c₀ ^ 2 ∈ s.C₂ := pow_mem hc₀C 2
  have hc0sqP : c₀ ^ 2 ∈ f3P s := by
    have hY : c₀ ^ 2 ∈ f3Y s := f3_C₂_le_Y hH hc0sq_C
    have hphi2 : f3phi s (c₀ ^ 2) = 1 := by
      rw [pow_two, f3_phi_mul hH c₀ hc₀Y c₀ hc₀Y, hphic0, hz2]
    rw [← f3_C₂_inf_X0 hH]
    exact ⟨hc0sq_C, (f3_phi_eq_one hH (c₀ ^ 2) hY).mp hphi2⟩
  have hc0sqB : c₀ ^ 2 ∈ s.fr.B := by
    have hL : c₀ ^ 2 ∈ L := s3_S_le_L s hc0sq_S
    rw [← f3_P_inf_L hH]
    exact ⟨hc0sqP, hL⟩
  exact ⟨c₀, hc₀C, by rw [hphic0]; exact y4_z_ne_one c, hc0sqB⟩

end CFSG.OddStandard.HigherRank.YamadaG23
