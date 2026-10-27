module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentP6
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding.U62ThreeCent

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

theorem nonempty_equiv_P6 {L : Type} [Group L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUSixTwoIndex d) (h : Nonempty (L ≃* CatGroup d)) : Nonempty (L ≃* P6) := by
  obtain ⟨q, hp2, he1, hdq⟩ := hd
  obtain ⟨x', hv⟩ := d
  obtain rfl : x' = TauCeti.LieTypeIndex.twistedA 5 q := hdq
  obtain ⟨e⟩ := h
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv e
  rw [hp2, he1] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm
  have e'' : L ≃* StatedProj (StatedSU 6 (2 ^ 1) K) := e'
  have := Fintype.ofFinite K
  have := Fintype.ofFinite F4
  have hcard : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, card_F4]
    norm_num
  have hreal := (unitary_prime_form_full_semilinear_realization uData hC6 hn6 hq6).1
  exact ⟨e''.trans ((CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hcard) 6 (2 ^ 1)).trans
      ((unitaryPSUEquiv uData (by norm_num)).symm.trans (Classical.choice hreal).symm))⟩

theorem u62ThreeCent {L : Type} [Group L] [Finite L] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUSixTwoIndex d) (h : Nonempty (L ≃* CatGroup d)) {x : L} (hx : orderOf x = 3) :
    (∃ E : Subgroup L, E ≤ Subgroup.centralizer {x} ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4) ∧
    ∃ Y : Subgroup L, Y ≤ Subgroup.centralizer {x} ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ^ 5 := by
  obtain ⟨e⟩ := nonempty_equiv_P6 hd h
  have h1 : HasLarge (e x) := hasLarge_of_orderOf_eq_three (by rw [MulEquiv.orderOf_eq, hx])
  have h2 : HasLarge x := by simpa using h1.map e.symm
  obtain ⟨⟨E, hEC, hEc, hE3, hEcard⟩, Y, hYC, hYp, hYcard⟩ := h2
  exact ⟨⟨E, hEC, ⟨hEc, hE3⟩, hEcard⟩, Y, hYC, hYp, hYcard⟩

end CFSG.AGLEmbedding.U62ThreeCent
