module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3GlueC

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem M10Config.exists_mem_zD {K : Type} [Group K] [Finite K] {z : K} {D : Subgroup K}
    (h : M10Config z D) {k : K} (hkz : k * z * k⁻¹ * z⁻¹ ∈ fusionOddCore K)
    (hk2 : k * k ∈ fusionOddCore K) :
    ∃ d ∈ D, ∃ j : ℤ, (z ^ j * d)⁻¹ * k ∈ fusionOddCore K := by
  have hkmem : (QuotientGroup.mk k : K ⧸ fusionOddCore K) ∈
      centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
        Set (K ⧸ fusionOddCore K)) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : (QuotientGroup.mk (k * z * k⁻¹ * z⁻¹) : K ⧸ fusionOddCore K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hkz
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    calc (QuotientGroup.mk k : K ⧸ fusionOddCore K) * QuotientGroup.mk z
        = (QuotientGroup.mk k * QuotientGroup.mk z * (QuotientGroup.mk k)⁻¹ *
            (QuotientGroup.mk z)⁻¹) * QuotientGroup.mk z * QuotientGroup.mk k := by group
      _ = QuotientGroup.mk z * QuotientGroup.mk k := by rw [h1, one_mul]
  let kC : ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K))) := ⟨QuotientGroup.mk k, hkmem⟩
  have hkk : (QuotientGroup.mk k : K ⧸ fusionOddCore K) * QuotientGroup.mk k = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).2 hk2
  have hkkC : kC * kC = 1 := Subtype.ext hkk
  have hyy : (QuotientGroup.mk kC : ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K))) ⧸ fusionOddCore ↥(centralizer
        ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} : Set (K ⧸ fusionOddCore K)))) *
      QuotientGroup.mk kC = 1 := by
    rw [← QuotientGroup.mk_mul, hkkC, QuotientGroup.mk_one]
  obtain ⟨a, ha, w, hw, hyaw⟩ := h.a6Pair.mem_sup
    (h.no_outer_rho (QuotientGroup.mk kC) (by rw [hyy]; exact one_mem _))
  rw [Abar, Subgroup.mem_map] at ha
  obtain ⟨c, hc, hca⟩ := ha
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hw
  have hy_eq : (QuotientGroup.mk kC : ↥(centralizer ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} :
      Set (K ⧸ fusionOddCore K))) ⧸ fusionOddCore ↥(centralizer
        ({(QuotientGroup.mk z : K ⧸ fusionOddCore K)} : Set (K ⧸ fusionOddCore K)))) =
      QuotientGroup.mk (cMap z (c * (zC z) ^ j)) := by
    have h1 : rho z (c * (zC z) ^ j) = QuotientGroup.mk (cMap z (c * (zC z) ^ j)) := rfl
    rw [← h1, map_mul, map_zpow, hca, hj]
    exact hyaw
  have hkC_eq : kC = cMap z (c * (zC z) ^ j) := by
    have h1 := QuotientGroup.eq.1 hy_eq
    rw [h.fusionOddCore_hat_eq_bot, mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hmk : (QuotientGroup.mk k : K ⧸ fusionOddCore K) =
      QuotientGroup.mk ((c : K) * z ^ j) := by
    have h1 := congrArg Subtype.val hkC_eq
    rw [cMap_val, Subgroup.coe_mul, Subgroup.coe_zpow] at h1
    exact h1
  have hD : (c : K) ∈ D := mem_subgroupOf.1 hc
  have hcomm : Commute (c : K) z := mem_centralizer_singleton_iff.1 c.2
  have hcz : (c : K) * z ^ j = z ^ j * (c : K) := (hcomm.zpow_right j).eq
  refine ⟨(c : K), hD, j, ?_⟩
  have h2 := QuotientGroup.eq.1 hmk.symm
  rw [hcz] at h2
  exact h2

end CFSG.EvenSporadicStandard.Fin76b
