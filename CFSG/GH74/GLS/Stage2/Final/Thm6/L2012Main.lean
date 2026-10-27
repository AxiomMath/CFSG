module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Fused
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012NFFinal

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open CFSG.GH74.GLS.Stage2.Final.Thm6

theorem lemma20_12_of_11
    (h11 : Lemma20_11) : Lemma20_12 := by
  intro G _ _ z k S M hF hMC hT
  rcases hT with ⟨ε, q, hTL⟩ | ⟨q, hpsp⟩
  · exfalso
    by_cases hfused : Fused ε q
    · exact fused_false h11 hF hMC hTL hfused
    · exact nonfused_false h11 hF hMC hTL hfused
  · have hpsp' : ∃ q : ℕ, TypePSp4 z k S q := ⟨q, hpsp⟩
    obtain ⟨hb, hc⟩ := psp4_bc h11 hF hMC hpsp'
    exact ⟨Or.inr hpsp', hb, hc⟩

theorem lemma20_13_of_11
    (h11 : Lemma20_11) : Lemma20_13 := by
  intro G _ _ z k S M hF hMC hnf
  obtain ⟨ε, q, hTL, hn⟩ := hnf
  exact (nonfused_false h11 hF hMC hTL hn).elim

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
