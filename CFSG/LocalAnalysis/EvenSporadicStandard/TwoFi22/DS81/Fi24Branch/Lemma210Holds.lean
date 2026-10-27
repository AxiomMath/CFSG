module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemma210
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemma210Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemma210Spor
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemma210Even
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Lemma210Odd

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

theorem ds81Lemma210Strong_holds
    : DS81Lemma210Strong := by
  intro B _ _ Y _ hna hcat hext h19 h21 y hy hy2 A hA _ _ hcent hquot
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition ↥Y hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | hspor
  · exact ds81Lemma210_alt hn θ h19 h21
  · exact ds81Lemma210_odd Y hna hodd y hy hy2 A hA hcent hquot
  · exact ds81Lemma210_even heven hext h19 h21
  · exact ds81Lemma210_spor hspor h19 h21

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
