module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_mem_Qz_isConj {G : Type} [Group G] {a z : G} (hF1 : Fusion1Facts a z) :
    ∃ q : G, q ∈ Qz z ∧ IsConj a q := by
  obtain ⟨z₀, b, u, _hF, hz₀, _hz₀a, _hz₀d, haQ, _hpCore, _hshape⟩ := hF1.rep_z
  obtain ⟨c, hc⟩ := isConj_iff.mp hz₀
  refine ⟨c⁻¹ * a * c, ?_, ?_⟩
  · have h : c * (c⁻¹ * a * c) * c⁻¹ ∈ Qz (c * z * c⁻¹) := by
      rw [hc, show c * (c⁻¹ * a * c) * c⁻¹ = a by group]
      exact haQ
    exact (Qz_conj_mem_iff (x := z) (y := c⁻¹ * a * c) c).mp h
  · exact isConj_iff.mpr ⟨c⁻¹, by group⟩

theorem exists_mem_Gx_not_mem_Qz {G : Type} [Group G] {a z : G} (hF1 : Fusion1Facts a z)
    (hF2 : Fusion2Facts a z) :
    ∃ q : G, q ∈ Gx z ∧ q ∉ Qz z ∧ IsConj a q := by
  obtain ⟨z₀, b, u, hF, hz₀, _hz₀a, _hz₀d, _haQ, _hpCore, _hshape⟩ := hF1.rep_z
  have hbu := hF2.reps_bu z₀ b u hF hz₀
  have huB : IsConj z (u : G) := hbu.2.1
  have hauQ : a ∉ Qz (u : G) := hbu.2.2.2.1
  obtain ⟨c, hc⟩ := isConj_iff.mp huB.symm
  have hcomm : a * (u : G) = (u : G) * a := mem_Gx.mp u.2
  refine ⟨c * a * c⁻¹, ?_, ?_, isConj_iff.mpr ⟨c, by group⟩⟩
  · rw [mem_Gx]
    rw [← hc]
    calc c * (u : G) * c⁻¹ * (c * a * c⁻¹)
        = c * ((u : G) * a) * c⁻¹ := by group
      _ = c * (a * (u : G)) * c⁻¹ := by rw [hcomm]
      _ = c * a * c⁻¹ * (c * (u : G) * c⁻¹) := by group
  · intro hq
    have h : a ∈ Qz (u : G) := (Qz_conj_mem_iff (x := (u : G)) (y := a) c).mp (by rwa [← hc] at hq)
    exact hauQ h

end CFSG.EvenSporadicStandard.HNRecog.Section3
