module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.T6A

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

theorem c19_2 (p f : ℕ) [Fact p.Prime] : Asc77.C19_2 p f := by
  intro G _ _ _ Ω K hs he W hW
  have hP : PartIHyp p f Ω := ⟨hs.odd, hs.five, hs.hyp, hs.aEmpty⟩
  by_cases h : ∃ J ∈ Ω, (omegaStarNbr Ω J).Nonempty
  · exact Or.inr (MuTab.muIsoS3_of_shape hP hW he h)
  · refine Or.inl (MuTab.muIsoZ2_of_shape hP hW ⟨K, hs.mem⟩ fun J hJ => ?_)
    exact Set.not_nonempty_iff_eq_empty.mp fun hne => h ⟨J, hJ, hne⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.T6A
