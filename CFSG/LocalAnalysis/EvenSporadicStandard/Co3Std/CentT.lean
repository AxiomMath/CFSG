module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.FS79Excluded
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.Swap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDCat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.OddIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Push

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

section Certified


theorem fs79Co3Excluded_of_catalog (hKD : KDCo3Cat) : FS79Co3Excluded := by
  intro G _ _ L h hL
  haveI := h.simple
  obtain ⟨z, t, T₀, P, x, hcfg, hP, hTP, hx, hxT, -, hxz, hxt⟩ := co3_inner_swap h hL
  have hT₀ : Nat.card T₀ = 2 ^ 10 := card_T₀_eq hcfg hL
  obtain ⟨Q, hQ, hQdvd⟩ := exists_sylow_le_centralizer hcfg hP hTP hx hxT hxz hxt
  have hdvd : 2 ^ 12 ∣ Nat.card ↥(centralizer ({t} : Set G)) := by
    have h1 : 2 ^ 12 ∣ Nat.card Q := by
      have : (2 : ℕ) ^ 12 = 4 * Nat.card T₀ := by rw [hT₀]; norm_num
      rwa [this]
    exact h1.trans (Subgroup.card_dvd_of_le hQ)
  have hzt : t * z = z * t := hcfg.z_comm_of_mem_A hcfg.t_mem_A
  have hzH : z ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have htH : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hconf := centConfig_of_inner h hL hcfg hT₀ hdvd ⟨z, hzH⟩ ⟨t, htH⟩ rfl rfl
  have hTW := hconf.transferWitness hKD
  exact false_of_transferWitness h.nonabelian Q hQ ⟨z, hzH⟩ hcfg.z_order hTW

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
