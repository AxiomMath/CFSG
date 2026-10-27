module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Finkelstein55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Eight55

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t z : G}

section Certified


theorem Setting.centralizer_eq_of_finkelstein_B (h : Setting G L t)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25) :
    centralizer ({t} : Set G) = L := by
  obtain ⟨e⟩ := h.quot_B
  obtain ⟨E, hE1, hE2⟩ := exists_isElemAbelian_eight_B
  have hI' : HypothesisOne (↥L ⧸ center ↥L) :=
    CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI
  have hE' := isElemAbelian_map_mulEquiv e.symm hE1
  have hcard : Nat.card (E.map e.symm.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE2]
  have hrank : 3 ≤ CFSG.Open.twoRank (↥L ⧸ center ↥L) :=
    Finkelstein77.three_le_twoRank_of_elemAbelian_eight _ hE' hcard
  exact h.centralizer_eq_of_finkelstein hI' hrank h25

theorem Setting.exists_level55_of_finkelstein (h : Setting G L t) (hc : CentralPair G L t z)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25) :
    Nonempty (Level55 G t z) :=
  h.exists_level55 hc (h.centralizer_eq_of_finkelstein_B hI h25)

end Certified

end CFSG.EvenSporadicStandard.TwoB
