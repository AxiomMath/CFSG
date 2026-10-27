module

public import CFSG.ClassicalInvolution.Asc77.AscT8YA2
public import CFSG.ClassicalInvolution.Asc77.AscT8X5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8YY

variable (p f : ℕ) [Fact p.Prime]


theorem w2caseA_of_caseB (hB : T8X.W2CaseB p f) : T8X.W2CaseA p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne hconn
  by_cases huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      DConnected (T8.layerFamQ Ω (z * s))
  · exact false_of_caseA_uniform hs hdisc hμ hne hconn huni
  · push Not at huni
    obtain ⟨M, hM, s, hs', hnconn⟩ := huni
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := muIsoWylD4_transfer hs.stand.odd hs.stand.five hs.stand.hyp hs.hW.1 hstd.hW.1 hμ
    obtain ⟨A, hAS, hA1, hAab, hAsc⟩ := hB G Ω K M S' R' T' W' z s hstd hdisc hμ' hne hnconn
    exact (l17_8 (p := p) (f := f)) G Ω K hs.stand S' A hAS hA1 hAab hAsc

theorem c26_13_sc_of_caseB (hB : T8X.W2CaseB p f) : C26_13_sc p f :=
  T8X.c26_13_sc_of_cases (w2caseA_of_caseB p f hB) hB

end T8YY

end CFSG.ClassicalInvolution.Asc77
