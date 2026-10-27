module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma55
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem isElemAbelian_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.map e.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _

section Certified


theorem ds81Lemma55CentralizerEq_of_finkelstein (hI : HypothesisOne (Carrier .B))
    (hE : ∃ E : Subgroup (Carrier .B), CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8)
    (h25 : Finkelstein77.Asc76Lemma25) : DS81Lemma55CentralizerEq := by
  intro G _ _ L t z h hc h54
  obtain ⟨e⟩ := h.quot_B
  obtain ⟨E, hE1, hE2⟩ := hE
  have hI' : HypothesisOne (↥L ⧸ center ↥L) :=
    CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hI
  have hE' := isElemAbelian_map_mulEquiv e.symm hE1
  have hcard : Nat.card (E.map e.symm.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE2]
  have hrank : 3 ≤ CFSG.Open.twoRank (↥L ⧸ center ↥L) :=
    Finkelstein77.three_le_twoRank_of_elemAbelian_eight _ hE' hcard
  exact h.centralizer_eq_of_finkelstein hI' hrank h25

end Certified

end CFSG.EvenSporadicStandard.TwoB
