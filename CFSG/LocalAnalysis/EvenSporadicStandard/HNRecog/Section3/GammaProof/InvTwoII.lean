module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvFourA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_inv_two_ii (H : GammaHyps a z) {t b : G} (hb : b ∈ orb2A a a) (ht : IsConj a t)
    (htb : t ∈ orb4A a z b) : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxy a t := by
  have hbt : b ∈ orb4A t z t := by
    refine ⟨ht.symm.trans hb.1, ?_⟩
    have e : (t * b) ^ 2 = t * (b * t) ^ 2 * t⁻¹ := by
      simp only [pow_two, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact htb.2.trans (isConj_iff.mpr ⟨t, rfl⟩)
  have hab : a ∈ orb2A t b := by
    refine ⟨ht.symm, ?_⟩
    rw [← H.comm_of_orb2A (IsConj.refl a) hb]
    exact ht.symm.trans hb.2
  obtain ⟨s, hs, hsG⟩ := gamma_inv_fourA (H.at ht) hbt hab
  rw [mem_Gxyz] at hsG
  exact ⟨s, hs, mem_Gxy.2 ⟨hsG.2.2, hsG.1⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
