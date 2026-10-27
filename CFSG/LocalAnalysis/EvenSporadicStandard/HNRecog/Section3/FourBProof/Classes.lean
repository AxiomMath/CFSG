module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Nonempty

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p q : G}

theorem fourB_classes (H : FourBHyps a z) (P : FourBPair a p q) :
    IsOrbitPartition (Gxy p q) {t | t ∈ Gxy p q ∧ orderOf t = 2} (fourBSetP a z p q) := by
  obtain ⟨r, hr⟩ := fourB_exists_reps (fourB_shape_K H P)
  exact fourB_pigeon (Gxy p q) {t | t ∈ Gxy p q ∧ orderOf t = 2} (fourBSetP a z p q) r
    (fun t ht => hr t ht.1 ht.2) (fourB_set_subset H P)
    (fun t ht => fourB_cover H P ht.1 ht.2) (fourB_set_disjoint H P)
    (fun i => fourB_set_conj i) (fourB_set_nonempty H P)

end CFSG.EvenSporadicStandard.HNRecog.Section3
