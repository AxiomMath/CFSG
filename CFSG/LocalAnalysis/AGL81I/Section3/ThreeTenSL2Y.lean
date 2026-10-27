module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL2Vacuity
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn)
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)

variable {H : Type} [Group H] [Finite H]

theorem d_le_Y_of_threeTenHyp {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) : D ≤ Y := by
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  haveI : Fact d.Prime := ⟨hd⟩
  have hdvd : d ∣ Nat.card D := by
    rcases hD.isPGroup.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hDne
    · exact h1
  have hpos : 1 ≤ CFSG.Open.pRank d (D.subgroupOf (I ⊔ D)) := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf d
      (le_sup_right : D ≤ I ⊔ D)]
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact CFSG.one_le_pRank_of_dvd_card hd hdvd
  intro x hx
  have hxT : x ∈ I ⊔ D := (le_sup_right : D ≤ I ⊔ D) hx
  let y : D.subgroupOf (I ⊔ D) := ⟨⟨x, hxT⟩, hx⟩
  have hnorm : Subgroup.normalizer
      ((D.subgroupOf (I ⊔ D) : Subgroup ↥(I ⊔ D)) : Set ↥(I ⊔ D)) ≤
      CFSG.Open.GLBCore d 1 (D.subgroupOf (I ⊔ D)) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.le_GLBCore_of_le_normalizer
      (p := d) (k := 1) le_rfl hpos le_rfl
  have hyN : y.1 ∈ Subgroup.normalizer
      ((D.subgroupOf (I ⊔ D) : Subgroup ↥(I ⊔ D)) : Set ↥(I ⊔ D)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact (D.subgroupOf (I ⊔ D)).mul_mem
        ((D.subgroupOf (I ⊔ D)).mul_mem y.2 hn) ((D.subgroupOf (I ⊔ D)).inv_mem y.2)
    · intro hn
      have h : y.1⁻¹ * (y.1 * n * y.1⁻¹) * y.1 ∈ D.subgroupOf (I ⊔ D) :=
        (D.subgroupOf (I ⊔ D)).mul_mem
          ((D.subgroupOf (I ⊔ D)).mul_mem ((D.subgroupOf (I ⊔ D)).inv_mem y.2) hn) y.2
      have heq : y.1⁻¹ * (y.1 * n * y.1⁻¹) * y.1 = n := by group
      rwa [heq] at h
  refine hγ (Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, ?_, rfl⟩)
  exact hnorm hyN

theorem threeTenSL2Vacuity_of_I_le_Y
    (h : ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
      ThreeTenHyp I D P Y p d →
      (IsSLType 2 (ZMod p) ↥I ∨ IsPSLType 2 (ZMod p) ↥I) → I ≤ Y) :
    ThreeTenSL2Vacuity := by
  intro H _ _ I D P Y p d hhyp htype
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hIY : I ≤ Y := h H I D P Y p d ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ htype
  have hDY : D ≤ Y := d_le_Y_of_threeTenHyp ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
  exact not_le_of_gt hYlt (sup_le hIY hDY)

end CFSG.LocalAnalysis.AGL81I.Section3
