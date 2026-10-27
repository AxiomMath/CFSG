module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

variable {H : Type} [Group H] [Finite H]

theorem normalizer_D_inter_le_Y {I D P Y : Subgroup H} {p d : ℕ}
    (hhyp : ThreeTenHyp I D P Y p d) :
    Subgroup.normalizer (D : Set H) ⊓ (I ⊔ D) ≤ Y := by
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
  have hxT : x ∈ I ⊔ D := hx.2
  let y : ↥(I ⊔ D) := ⟨x, hxT⟩
  have hyN : y ∈ Subgroup.normalizer
      ((D.subgroupOf (I ⊔ D) : Subgroup ↥(I ⊔ D)) : Set ↥(I ⊔ D)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (le_sup_right : D ≤ I ⊔ D)]
    rw [Subgroup.mem_subgroupOf]
    exact hx.1
  have hcore : y ∈ CFSG.Open.GLBCore d 1 (D.subgroupOf (I ⊔ D)) :=
    (CFSG.HardMathSupport.Timmesfeld.Proving.le_GLBCore_of_le_normalizer
      (p := d) (k := 1) le_rfl hpos le_rfl) hyN
  exact hγ (Subgroup.mem_map.mpr ⟨y, hcore, rfl⟩)

end CFSG.LocalAnalysis.AGL81I.Section3
