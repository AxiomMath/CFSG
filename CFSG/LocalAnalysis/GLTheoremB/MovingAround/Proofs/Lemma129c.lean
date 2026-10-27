module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129h
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129i
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129j
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129k

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf autBar barAut innerAut)
open Lemma129

theorem lemma129_printed_of_inputs (h121 : Prop121_corStatement) (h128 : Lemma128Statement)
    (h191 : Input19_1_6) (hI : Input19_1_two) (h1916 : Input19_16Main) (h23 : Lemma129e.Input23_5)
    (h239 : Lemma129k.Input23_9) : Lemma129PrintedStatement := by
  intro G _ _ m p B M E A N D h
  obtain ⟨S, F, K, hs⟩ := exists_setup2 h191 h121 hI h
  have hp := prime_of h
  have hFel : IsElemAbelian p F := (A_el h).mono hs.F_le_A
  rcases apply_input1916Main h1916 h hs.hK hs.hr (isElemAbelian_autBar hs.hFK hFel)
      (by rw [card_autBar p hs.hFK hs.hFc, card_eq_pow_pRank hp hFel]) with
    hbal | halt | hspor | hlie
  · exact absurd hbal hs.hbal
  · obtain ⟨D'⟩ := Lemma129d.exists_altData h hs halt
    have hAK := Lemma129i.alt_norm h23 h hs D'
    have hr2 := Lemma129k.alt_rank_two h239 h23 h121 h hs D' hAK
    obtain ⟨hcom, hdata⟩ := Lemma129h.alt_case_of_norm h23 h121 h hs D' hAK hr2
      (Lemma129j.alt_E5 h128 h23 h121 h hs D' hAK hr2)
    exact ⟨K, hcom, Or.inl hdata⟩
  · have hr2 : CFSG.Open.pRank p F = 2 := hspor.2.1
    rw [hr2] at hspor
    obtain ⟨hcom, htype⟩ := Lemma129b.lemma129_bc h121 h hs hr2 (Or.inl hspor)
    exact ⟨K, hcom, Or.inr htype⟩
  · have hr2 : CFSG.Open.pRank p F = 2 := hlie.1
    rw [hr2] at hlie
    obtain ⟨hcom, htype⟩ := Lemma129b.lemma129_bc h121 h hs hr2 (Or.inr hlie)
    exact ⟨K, hcom, Or.inr htype⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
