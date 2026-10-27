module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchEnd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1CornerB

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Corner

theorem szEightCorner : SzEightCorner := by
  intro G _ _ L a t T d V U U₁ k h hlam hμ hν hU
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  obtain ⟨-, -, h168, hsimple⟩ := h.corner_of_nu_ne_zero hK hc hκ hμ hlam hν
  have hbig : 2 ^ 3 < Nat.card (h.famPerm hK hc hμ hlam).range := by rw [h168]; norm_num
  have hA : ∀ n ∈ normalizer (U : Set G), n ^ 2 = 1 →
      (∀ b ∈ szA₁ (szT₁ L T), n * b * n⁻¹ = b) → n ∈ U :=
    fun n hn _ hcen => h.mem_U_of_centralizes hK hc hκ hμ hlam hν hU hsimple hbig hn hcen
  have hodd := h.not_two_dvd_index_normalizer hK hc rfl hκ hμ hlam hν hU hA
  obtain ⟨K₀, hK₀N, hK₀n, hab, hU₁K, htK⟩ := h.exists_det_ker rfl hμ
  have : IsSimpleGroup G := h.start.setting.1
  refine SzCorner.false_of_transfer h.start.setting.2.1 hodd hK₀N hK₀n hab
    (le_normalizer h.t_mem_U) htK h.start.inv fun g hg => ?_
  have hU₁ := h.conj_mul_t_mem_U₁ hμ hlam hA g⁻¹ (by rw [inv_inv]; exact hg)
  rw [inv_inv] at hU₁
  apply hU₁K
  have e : t⁻¹ * (g⁻¹ * t * g) = t * (g⁻¹ * t * g * t) * t⁻¹ := by
    calc t⁻¹ * (g⁻¹ * t * g) = t * (g⁻¹ * t * g) := by rw [h.t_inv]
      _ = t * (g⁻¹ * t * g * t) * t⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp h.t_mem_normalizer_U₁ _).mp hU₁

end Corner

end CFSG.SeitzReduction.RankOne
