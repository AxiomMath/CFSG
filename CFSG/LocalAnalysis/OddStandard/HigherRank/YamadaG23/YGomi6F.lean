module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiData

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem ne_top_of_gomi6data {G : Type} [Group G] [Finite G] {A V C₀ C₁ : Subgroup G} {t u : G}
    (h : Gomi6Data A V C₀ C₁ t u) {Hh : Subgroup G}
    (hle : Hh ≤ Subgroup.centralizer (V : Set G)) : Hh ≠ ⊤ := by
  rintro rfl
  have htc : t ∈ Subgroup.centralizer (V : Set G) := hle (Subgroup.mem_top t)
  have huV : u ∈ V := h.V_eq ▸ Subgroup.mem_zpowers u
  have hcomm : u * t = t * u := Subgroup.mem_centralizer_iff.mp htc u huV
  have h1 : u = u⁻¹ := by
    calc u = t * u * t⁻¹ := by rw [← hcomm]; group
      _ = u⁻¹ := h.t_inv
  have h2 : u ^ 2 = 1 := by
    have : u * u = 1 := by
      nth_rewrite 1 [h1]
      exact inv_mul_cancel u
    simpa [pow_two] using this
  have h3 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [h.u_order] at h3
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
