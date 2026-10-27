module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T : Subgroup G}

theorem fzr_x_exists_x1 (h : FzStr t tau lam rho Z E W Q R T) :
    ∃ x1 ∈ E, x1⁻¹ * (lam * x1 * lam⁻¹) ∉ Z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz, hlz⟩ := h.lam_Z
  obtain ⟨e, he, hez⟩ := h.Z_sqrt z hz
  have hz' : e⁻¹ * (lam * e * lam⁻¹) ∈ Z := hcon e he
  have hle : lam * e * lam⁻¹ = e * (e⁻¹ * (lam * e * lam⁻¹)) := by group
  have hcomm : Commute e (e⁻¹ * (lam * e * lam⁻¹)) :=
    h.W_comm e (h.EW he) _ (h.EW (h.ZE hz'))
  apply hlz
  calc lam * z * lam⁻¹ = (lam * e * lam⁻¹) ^ 2 := by rw [conj_pow, hez]
    _ = (e * (e⁻¹ * (lam * e * lam⁻¹))) ^ 2 := by rw [← hle]
    _ = e ^ 2 * (e⁻¹ * (lam * e * lam⁻¹)) ^ 2 := hcomm.mul_pow 2
    _ = z := by rw [h.Z_sq _ hz', mul_one, hez]

end CFSG.OddStandard.SmallF3.FritzII
