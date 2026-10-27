module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace OddCentralCover

variable {A P : Type*} [Group A] [Group P] {ρ : A →* P}

theorem commute_of_mul_self_eq_one (h : OddCentralCover ρ) {a b : A} (ha : a * a = 1)
    (hb : b * b = 1) (hab : ρ a * ρ b = ρ b * ρ a) : a * b = b * a := by
  have ha' : a⁻¹ = a := (mul_eq_one_iff_eq_inv.mp ha).symm
  have hb' : b⁻¹ = b := (mul_eq_one_iff_eq_inv.mp hb).symm
  have hρa : ρ a * ρ a = 1 := by rw [← map_mul, ha, map_one]
  have hρb : ρ b * ρ b = 1 := by rw [← map_mul, hb, map_one]
  have hc : (a * b) * (a * b) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul]
    calc ρ a * ρ b * (ρ a * ρ b) = ρ a * (ρ b * ρ a) * ρ b := by group
      _ = ρ a * (ρ a * ρ b) * ρ b := by rw [hab]
      _ = (ρ a * ρ a) * (ρ b * ρ b) := by group
      _ = 1 := by rw [hρa, hρb, one_mul]
  have hcent : (a * b) * (a * b) ∈ Subgroup.center A := h.ker_le_center hc
  have h1 : a * ((a * b) * (a * b)) * a⁻¹ = (a * b) * (a * b) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_center_iff.mp hcent a
  have h2 : a * ((a * b) * (a * b)) * a⁻¹ = (b * a) * (b * a) := by
    calc a * ((a * b) * (a * b)) * a⁻¹ = (a * a) * b * (a * b) * a := by rw [ha']; group
      _ = (b * a) * (b * a) := by rw [ha]; group
  have h3 : (a * b) * (a * b) = (b * a) * (b * a) := h1.symm.trans h2
  have hba : b * a = (a * b)⁻¹ := by rw [mul_inv_rev, ha', hb']
  have h4 : ((a * b) * (a * b)) * ((a * b) * (a * b)) = 1 := by
    have e : (a * b) * (a * b) = (a * b)⁻¹ * (a * b)⁻¹ := by rw [← hba]; exact h3
    calc ((a * b) * (a * b)) * ((a * b) * (a * b))
        = ((a * b) * (a * b)) * ((a * b)⁻¹ * (a * b)⁻¹) := by rw [← e]
      _ = 1 := by group
  have h5 : (a * b) * (a * b) = 1 := h.eq_one_of_mul_self_eq_one hc h4
  have h6 : (a * b)⁻¹ = a * b := (mul_eq_one_iff_eq_inv.mp h5).symm
  rw [mul_inv_rev, ha', hb'] at h6
  exact h6.symm

end OddCentralCover

end CFSG.OddStandard.SmallF3.Omega
