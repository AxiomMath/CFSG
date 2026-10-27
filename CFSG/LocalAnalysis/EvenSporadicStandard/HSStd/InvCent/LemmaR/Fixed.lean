module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.EvenSporadicStandard.SolomonRed

theorem setting_le_of_fixedData {K : Type*} [Group K] [Finite K] {z : K} {B S : Subgroup K}
    (h : Setting K z B) (hS : FixedData K S) : B ≤ S := by
  have hMnorm : ∀ b ∈ B, ∀ x ∈ S ⊓ centralizer ({z} : Set K),
      b * x * b⁻¹ ∈ S ⊓ centralizer ({z} : Set K) := by
    intro b hb x hx
    refine ⟨hS.normal.conj_mem x hx.1 b, ?_⟩
    exact (centralizer ({z} : Set K)).mul_mem
      ((centralizer ({z} : Set K)).mul_mem (h.le_cent hb) hx.2)
      ((centralizer ({z} : Set K)).inv_mem (h.le_cent hb))
  rcases inf_eq_bot_or_le_of_simple h.simple hMnorm with hbot | hle
  · exfalso
    have hEn : ∀ g x : K, x ∈ S → g * x * g⁻¹ ∈ S := fun g x hx => hS.normal.conj_mem x hx g
    have hMz := inf_le_zpowers_of_inf_eq_bot h hEn hbot
    have hzS : z ∉ S := by
      intro hz
      obtain ⟨x, hxS, hxz, hxn⟩ := exists_commute_not_mem_zpowers
        (isPerfect_of_simple_of_nonab hS.simple hS.nonab) hz h.z_sq h.z_ne
      exact hxn (hMz x ⟨hxS, Setting.mem_cent_iff.2 hxz⟩)
    have hfix : ∀ w ∈ S, z * w = w * z → w = 1 := by
      intro w hw hwz
      rcases (mem_zpowers_iff_of_mul_self_eq_one h.z_sq).1
        (hMz w ⟨hw, Setting.mem_cent_iff.2 hwz.symm⟩) with h1 | h1
      · exact h1
      · exact absurd (h1 ▸ hw) hzS
    obtain ⟨a, ha, b, hb, hab⟩ := hS.nonab
    exact hab (fixedPointFree_commute_of_mul_self_eq_one h.z_sq
      (fun w hw => hS.normal.conj_mem w hw z) hfix a ha b hb)
  · exact fun b hb => (hle hb).1

end CFSG.EvenSporadicStandard.HSStd.InvCent
