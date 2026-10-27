module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma512K_of (fact : Asc82Fact512K) : Asc82Lemma512K := by
  intro G _ _ t L S z r B A hr hc
  obtain ⟨K₁, K₂, h1, h2, hne, hcomm, i1, i2, hprod⟩ :=
    fact G L hr.toSec5Setting.isOm6Z2 t hr.involution hc z hr.pocket
  exact ⟨K₁, K₂,
    { toSec5RCtx := hr
      centre := hc
      pocket₁ := h1
      pocket₂ := h2
      ne := hne
      comm := hcomm
      iso₁ := i1
      iso₂ := i2
      prod := hprod }⟩

end CFSG.OddStandard.SmallF3.Omega
