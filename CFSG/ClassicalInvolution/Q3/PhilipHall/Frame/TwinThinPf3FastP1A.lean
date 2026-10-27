module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem mem_P1 : ∀ w ∈ [dataP1.a, dataP1.b, dataP1.c, dataP1.d, dataP1.h],
    wsum w = 0 ∧ Equiv.Perm.sign w.perm = 1 ∧ ∀ s ∈ affinePlanes,
      s.map w.perm.toEmbedding ∈ affinePlanes ∧ s.map w.perm⁻¹.toEmbedding ∈ affinePlanes := by
  decide +kernel

theorem rels_h_P1 : ∀ r ∈ dataP1.rels, eqPF (evalF (dataP1.gensF (ofWr dataP1.h)) r) oneF := by
  decide +kernel

theorem rels_cands_P1 : ∀ e ∈ dataP1.cands, ∀ r ∈ dataP1.rels,
    eqPF (evalF (dataP1.gensF (ofWr e.1)) r) oneF := by
  decide +kernel

theorem cand_words_P1 : ∀ e ∈ dataP1.cands,
    eqPF (evalF (dataP1.gensF (ofWr dataP1.h)) e.2) (ofWr e.1) := by
  decide +kernel

theorem dyn_P1 : ∀ e ∈ dataP1.cands, dataP1.inSF (ofWr e.1) ∧ dataP1.inSF (dataP1.stepF (ofWr e.1) (ofWr e.1)) ∧
    dataP1.inSF (dataP1.stepF (ofWr e.1) (dataP1.stepF (ofWr e.1) (ofWr e.1))) ∧
    eqPF (dataP1.stepF (ofWr e.1) (dataP1.stepF (ofWr e.1) (dataP1.stepF (ofWr e.1) (ofWr e.1))))
      (ofWr dataP1.h) := by
  decide +kernel

theorem perm_chk_P1 : chk (fun q t => decide (∀ x, pc t.1 x = qf q x)) quadsList
    dataP1.permWords = true := by
  decide +kernel

theorem permWords_ok_P1 : ∀ t ∈ dataP1.permWords,
    eqPF (evalF (dataP1.gensF (ofWr dataP1.h)) t.2) (ofWr (⟨0, pc t.1⟩ : Wr 8)) := by
  decide +kernel

theorem pairWords_ok_P1 : ∀ t ∈ dataP1.pairWords,
    eqPF (evalF (dataP1.gensF (ofWr dataP1.h)) t.2.2) (ofWr (ofVec (vecOf [t.1, t.2.1]))) := by
  decide +kernel

theorem pairs_cov_P1 : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ∀ q ∈ pairUp8 (supp8 v),
    ∃ t ∈ dataP1.pairWords, t.1 = q.1 ∧ t.2.1 = q.2 := by
  decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
