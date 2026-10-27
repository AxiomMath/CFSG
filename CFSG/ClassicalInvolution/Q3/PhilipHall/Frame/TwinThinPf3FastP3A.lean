module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem mem_P3 : ∀ w ∈ [dataP3.a, dataP3.b, dataP3.c, dataP3.d, dataP3.h],
    wsum w = 0 ∧ Equiv.Perm.sign w.perm = 1 ∧ ∀ s ∈ affinePlanes,
      s.map w.perm.toEmbedding ∈ affinePlanes ∧ s.map w.perm⁻¹.toEmbedding ∈ affinePlanes := by
  decide +kernel

theorem rels_h_P3 : ∀ r ∈ dataP3.rels, eqPF (evalF (dataP3.gensF (ofWr dataP3.h)) r) oneF := by
  decide +kernel

theorem rels_cands_P3 : ∀ e ∈ dataP3.cands, ∀ r ∈ dataP3.rels,
    eqPF (evalF (dataP3.gensF (ofWr e.1)) r) oneF := by
  decide +kernel

theorem cand_words_P3 : ∀ e ∈ dataP3.cands,
    eqPF (evalF (dataP3.gensF (ofWr dataP3.h)) e.2) (ofWr e.1) := by
  decide +kernel

theorem dyn_P3 : ∀ e ∈ dataP3.cands, dataP3.inSF (ofWr e.1) ∧ dataP3.inSF (dataP3.stepF (ofWr e.1) (ofWr e.1)) ∧
    dataP3.inSF (dataP3.stepF (ofWr e.1) (dataP3.stepF (ofWr e.1) (ofWr e.1))) ∧
    eqPF (dataP3.stepF (ofWr e.1) (dataP3.stepF (ofWr e.1) (dataP3.stepF (ofWr e.1) (ofWr e.1))))
      (ofWr dataP3.h) := by
  decide +kernel

theorem perm_chk_P3 : chk (fun q t => decide (∀ x, pc t.1 x = qf q x)) quadsList
    dataP3.permWords = true := by
  decide +kernel

theorem permWords_ok_P3 : ∀ t ∈ dataP3.permWords,
    eqPF (evalF (dataP3.gensF (ofWr dataP3.h)) t.2) (ofWr (⟨0, pc t.1⟩ : Wr 8)) := by
  decide +kernel

theorem pairWords_ok_P3 : ∀ t ∈ dataP3.pairWords,
    eqPF (evalF (dataP3.gensF (ofWr dataP3.h)) t.2.2) (ofWr (ofVec (vecOf [t.1, t.2.1]))) := by
  decide +kernel

theorem pairs_cov_P3 : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ∀ q ∈ pairUp8 (supp8 v),
    ∃ t ∈ dataP3.pairWords, t.1 = q.1 ∧ t.2.1 = q.2 := by
  decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
