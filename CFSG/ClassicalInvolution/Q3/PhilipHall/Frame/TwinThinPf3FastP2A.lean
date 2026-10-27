module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3DataP2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Bridge
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FilterN

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem mem_P2 : ∀ w ∈ [dataP2.a, dataP2.b, dataP2.c, dataP2.d, dataP2.h],
    wsum w = 0 ∧ Equiv.Perm.sign w.perm = 1 ∧ ∀ s ∈ affinePlanes,
      s.map w.perm.toEmbedding ∈ affinePlanes ∧ s.map w.perm⁻¹.toEmbedding ∈ affinePlanes := by
  decide +kernel

theorem rels_h_P2 : ∀ r ∈ dataP2.rels, eqPF (evalF (dataP2.gensF (ofWr dataP2.h)) r) oneF := by
  decide +kernel

theorem rels_cands_P2 : ∀ e ∈ dataP2.cands, ∀ r ∈ dataP2.rels,
    eqPF (evalF (dataP2.gensF (ofWr e.1)) r) oneF := by
  decide +kernel

theorem cand_words_P2 : ∀ e ∈ dataP2.cands,
    eqPF (evalF (dataP2.gensF (ofWr dataP2.h)) e.2) (ofWr e.1) := by
  decide +kernel

theorem dyn_P2 : ∀ e ∈ dataP2.cands, dataP2.inSF (ofWr e.1) ∧ dataP2.inSF (dataP2.stepF (ofWr e.1) (ofWr e.1)) ∧
    dataP2.inSF (dataP2.stepF (ofWr e.1) (dataP2.stepF (ofWr e.1) (ofWr e.1))) ∧
    eqPF (dataP2.stepF (ofWr e.1) (dataP2.stepF (ofWr e.1) (dataP2.stepF (ofWr e.1) (ofWr e.1))))
      (ofWr dataP2.h) := by
  decide +kernel

theorem perm_chk_P2 : chk (fun q t => decide (∀ x, pc t.1 x = qf q x)) quadsList
    dataP2.permWords = true := by
  decide +kernel

theorem permWords_ok_P2 : ∀ t ∈ dataP2.permWords,
    eqPF (evalF (dataP2.gensF (ofWr dataP2.h)) t.2) (ofWr (⟨0, pc t.1⟩ : Wr 8)) := by
  rw [show dataP2.gensF (ofWr dataP2.h) = List.map (fun x => FilterN.decP x.1 x.2)
      [(17, 267069840090634), (65, 257867905664908), (34, 206444460491416), (130, 132828985085608), (48, 16419952700487)] by decide +kernel]
  simp only [FilterN.evalF_decP]
  decide +kernel

theorem pairWords_ok_P2 : ∀ t ∈ dataP2.pairWords,
    eqPF (evalF (dataP2.gensF (ofWr dataP2.h)) t.2.2) (ofWr (ofVec (vecOf [t.1, t.2.1]))) := by
  decide +kernel

theorem pairs_cov_P2 : ∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ∀ q ∈ pairUp8 (supp8 v),
    ∃ t ∈ dataP2.pairWords, t.1 = q.1 ∧ t.2.1 = q.2 := by
  decide +kernel

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
