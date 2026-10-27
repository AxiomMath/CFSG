module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvFourB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvFourA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvFiveA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_inv_one (H : GammaHyps a z) {y t : G}
    (hy : y ∈ orb2A a a ∪ orb2B a z a ∪ orb4A a z a ∪ orb4B a a ∪ orb5A a a)
    (ht : t ∈ orb2A a y) : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz a y t := by
  rcases hy with (((hy | hy) | hy) | hy) | hy
  · exact ⟨y, H.orderOf_a hy.1, H.self_mem_Gxyz hy.1 (H.comm_of_orb2A (IsConj.refl a) hy) ht⟩
  · exact ⟨y, H.orderOf_a hy.1, H.self_mem_Gxyz hy.1 (H.comm_of_orb2B (IsConj.refl a) hy) ht⟩
  · exact gamma_inv_fourA H hy ht
  · exact gamma_inv_fourB H hy ht
  · exact gamma_inv_fiveA H hy ht

end CFSG.EvenSporadicStandard.HNRecog.Section3
