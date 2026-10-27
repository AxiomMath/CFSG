module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreSpor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

section Alternating

variable {X : Type} [Group X] [Finite X]

theorem k1Core_false_of_alternating {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) {n : ℕ} (hn : 5 ≤ n)
    (e : K ≃* (TauCeti.CFSGIndex.alternating n hn).Group) (hRA : (R : Subgroup X) ≠ A) :
    False := by
  have hn6 : n = 2 * 3 := h.eq_two_mul_of_alternating hn e
  have hRK := h.sylow_le_of_alternating hn e
  subst hn6
  apply hRA
  refine k1Core_sylow_eq_of_le h.toD2Reduced hRK ?_
  rw [Nat.card_congr e.toEquiv]
  show ¬ 27 ∣ Nat.card (alternatingGroup (Fin 6))
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

end Alternating

section Main


theorem k1Core_holds : K1Core := by
  intro X _ _ R A X₀ B hK hred _ hBR hB hBc hconj _ W hW hWc
  obtain ⟨K, h⟩ := k1Core_almostSimple hK hred
  have hBA : B ≠ A := k1Core_ne_of_conj hconj
  have hRA : (R : Subgroup X) ≠ A := fun hRA =>
    k1Core_false_of_sylow_eq hred hBR (by rw [hBc]; norm_num) hBA hRA
  have hAW : A ≤ Subgroup.normalizer (W : Set X) := le_sup_right.trans hW
  obtain ⟨i, ⟨e⟩⟩ := h.catalog
  cases i with
  | cyclic q hq => exact (h.false_of_cyclic q hq e).elim
  | alternating n hn => exact (k1Core_false_of_alternating h hn e hRA).elim
  | lie d => exact k1Core_eq_bot_of_lie h d e hBR hB hBc hconj hRA hAW hWc
  | sporadic s => exact (k1Core_false_of_sporadic h s e hRA).elim

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
