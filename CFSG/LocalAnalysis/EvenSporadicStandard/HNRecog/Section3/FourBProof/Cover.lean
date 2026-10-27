module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Pattern
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Sets

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

theorem fourB_cover (H : FourBHyps a z) (P : FourBPair a p q) {t : G} (ht : t ∈ Gxy p q)
    (ht2 : orderOf t = 2) : ∃ i, t ∈ fourBSetP a z p q i := by
  rcases fourB_cls_t H P ht ht2 with htA | htB <;>
    rcases fourB_cls_pt H P ht ht2 with hptA | hptB <;>
    rcases fourB_cls_qt H P ht ht2 with hqtA | hqtB
  · refine ⟨0, ?_⟩
    rw [fourB_AAA H P ht ht2 htA hptA hqtA]
    show (p * q) ^ 2 ∈ ({(p * q) ^ 2} : Set G)
    exact Set.mem_singleton _
  · refine ⟨3, ?_⟩
    show t ∈ orb2A a p ∩ orb2B a z q
    exact ⟨⟨htA, hptA⟩, ⟨htA, hqtB⟩⟩
  · refine ⟨5, ?_⟩
    show t ∈ orb2A a q ∩ orb2B a z p
    exact ⟨⟨htA, hqtA⟩, ⟨htA, hptB⟩⟩
  · refine ⟨1, ?_⟩
    show t ∈ orb2B a z p ∩ orb2B a z q
    exact ⟨⟨htA, hptB⟩, ⟨htA, hqtB⟩⟩
  · exact (fourB_no_BAA H P ht ht2 ⟨htB, hptA, hqtA⟩).elim
  · refine ⟨4, ?_⟩
    show t ∈ orb2AB a z p ∩ orb2BB a z q
    exact ⟨⟨htB, hptA⟩, ⟨htB, hqtB⟩⟩
  · refine ⟨6, ?_⟩
    show t ∈ orb2AB a z q ∩ orb2BB a z p
    exact ⟨⟨htB, hqtA⟩, ⟨htB, hptB⟩⟩
  · refine ⟨2, ?_⟩
    show t ∈ orb2BB a z p ∩ orb2BB a z q
    exact ⟨⟨htB, hptB⟩, ⟨htB, hqtB⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
