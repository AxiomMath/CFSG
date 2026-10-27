module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.E0
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelFuseFrame

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22.FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_E0_of_piC_mem
    {t : ↥Cd}
    (ht : piC t ∈ fjProj.range) : t ∈ E0 := by
  obtain ⟨w, hw⟩ := ht
  have he : (⟨fjHom w, fjHom_mem_Cd w⟩ : ↥Cd) ∈ E0 := Subgroup.mem_subgroupOf.2 ⟨w, rfl⟩
  have hd : dCd ∈ E0 := Subgroup.mem_subgroupOf.2 ⟨eVec 0, by rw [fjHom_eVec, fjPt_zero]; rfl⟩
  have hker : t * (⟨fjHom w, fjHom_mem_Cd w⟩ : ↥Cd)⁻¹ ∈ piC.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h : piC ⟨fjHom w, fjHom_mem_Cd w⟩ = piC t := hw
    rw [h, mul_inv_cancel]
  rw [ker_piC, center_C] at hker
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hker
  have e : t = dCd ^ k * (⟨fjHom w, fjHom_mem_Cd w⟩ : ↥Cd) := by rw [hk]; group
  rw [e]
  exact E0.mul_mem (E0.zpow_mem hd k) he

theorem E0_fuse :
    ∀ s : ↥Cd, orderOf s = 2 → ∃ l : ↥Cd, l⁻¹ * s * l ∈ E0 := by
  intro s hs
  by_cases h1 : piC s = 1
  · refine ⟨1, ?_⟩
    rw [inv_one, one_mul, mul_one]
    exact mem_E0_of_piC_mem (by rw [h1]; exact one_mem _)
  · have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
    have h2 : orderOf (piC s) = 2 := orderOf_eq_prime (by rw [← map_pow, hs2, map_one]) h1
    obtain ⟨h, hh⟩ := exists_conj_mem_range h2
    obtain ⟨l, rfl⟩ := piC_surjective h
    refine ⟨l⁻¹, ?_⟩
    refine mem_E0_of_piC_mem ?_
    simpa [map_mul, map_inv] using hh

end CFSG.EvenSporadicStandard.TwoFi22.DS81
