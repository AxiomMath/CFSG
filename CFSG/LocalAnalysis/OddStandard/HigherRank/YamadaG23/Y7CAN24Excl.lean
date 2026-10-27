module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Cent
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Gen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Wr
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Main

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.AltStdSmall4.GL62

theorem n24_excl (H : Subgroup (GL (Fin 6) (ZMod 2)))
    (hs : IsSimpleGroup ↥H) (hnc : ¬ ∀ x y : ↥H, x * y = y * x) (h64 : 2 ^ 6 ∣ Nat.card ↥H)
    (hD : (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range ≤ H)
    (hzH : ∀ h ∈ H, z₀ * h * z₀⁻¹ ∈ H)
    (hc : ∀ c ∈ H, c * z₀ = z₀ * c →
      ∀ d ∈ (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range,
        c * d * c⁻¹ ∈ (dg : GL (Fin 3) (ZMod 2) →* GL (Fin 6) (ZMod 2)).range) :
    False := by
  have hz0z0 : z₀ * z₀ = 1 := z0_mul_self
  have hz0B : z₀ ∈ B₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀)
  have hHX : H ≤ H ⊔ Subgroup.zpowers z₀ := le_sup_left
  have hz0X : z₀ ∈ H ⊔ Subgroup.zpowers z₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀)
  have hBX : B₀ ≤ H ⊔ Subgroup.zpowers z₀ :=
    sup_le (hD.trans hHX) (Subgroup.zpowers_le.2 hz0X)
  have hCX : ∀ x ∈ H ⊔ Subgroup.zpowers z₀, x * z₀ = z₀ * x → x ∈ B₀ := by
    intro x hx hxz
    rcases n24_sup_elems H z₀ hz0z0 hzH hx with hxH | ⟨h, hh, rfl⟩
    · exact n24_cent_norm x hxz (hc x hxH hxz)
    · have e : h = z₀ * h * z₀ := by
        calc h = h * (z₀ * z₀) := by rw [hz0z0, mul_one]
          _ = (h * z₀) * z₀ := by rw [mul_assoc]
          _ = z₀ * (h * z₀) := hxz
          _ = z₀ * h * z₀ := by rw [mul_assoc]
      have hhz : h * z₀ = z₀ * h := by
        calc h * z₀ = (z₀ * h * z₀) * z₀ := by rw [← e]
          _ = z₀ * h := by rw [mul_assoc, hz0z0, mul_one]
      exact B₀.mul_mem (n24_cent_norm h hhz (hc h hh hhz)) hz0B
  rcases gl62OvergroupsEq_holds _ hBX hCX with
    ⟨hXe, hcard⟩ | ⟨hXe, hcard⟩ | ⟨hXe, hcard⟩ | ⟨hXe, hcard⟩ | ⟨hXe, hcard⟩
  · have h1 := Subgroup.card_dvd_of_le hHX
    rw [hcard] at h1
    exact absurd (h64.trans h1) (by norm_num)
  · have h1 := Subgroup.card_dvd_of_le hHX
    rw [hcard] at h1
    exact absurd (h64.trans h1) (by norm_num)
  · have hHW : H ≤ MW := by rw [← hXe]; exact hHX
    exact absurd (h64.trans (n24_MW_card_dvd H hHW hs hnc)) (by norm_num)
  · have hHS : H ≤ MS := by rw [← hXe]; exact hHX
    have hcX : cGL ∈ H ⊔ Subgroup.zpowers z₀ := by rw [hXe]; exact n24_cGL_mem_MS
    have hcH : cGL ∈ H := n24_odd_mem H z₀ cGL hz0z0 hzH hcX cGL_pow_three
    exact n24_odd_contra H hs hnc cGL cGL_ne_one hcH (fun h hh => MS_le_normC (hHS hh))
  · have hHG : H ≤ MG := by rw [← hXe]; exact hHX
    have hcX : cGL ∈ H ⊔ Subgroup.zpowers z₀ := by rw [hXe]; exact n24_cGL_mem_MG
    have hcH : cGL ∈ H := n24_odd_mem H z₀ cGL hz0z0 hzH hcX cGL_pow_three
    exact n24_odd_contra H hs hnc cGL cGL_ne_one hcH (fun h hh => MG_le_normC (hHG hh))

end CFSG.OddStandard.HigherRank.YamadaG23
