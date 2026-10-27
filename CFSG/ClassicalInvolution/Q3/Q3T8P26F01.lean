module

public import CFSG.ClassicalInvolution.Q3.Q3T8P26B01
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRB
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

section Assembly


theorem T8YY.w2caseA3_of_caseB3 [Fact AlphaFrame3] (hB : T8X.W2CaseB3) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
      (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
        ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
          DConnected (Q3T7.layerFam3 Ω (z * t)) → False := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne hconn
  by_cases huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      DConnected (Q3T7.layerFam3 Ω (z * s))
  · exact T8YY.false_of_caseA_uniform hs hdisc hμ hne hconn huni
  · push Not at huni
    obtain ⟨M, hM, s, hs', hnconn⟩ := huni
    obtain ⟨S', R', T', W', hstd⟩ :=
      c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
    have hμ' := T8YY.muIsoWylD4_transfer hs.stand.modU hs.hW.1 hstd.hW.1 hμ
    exact hB G Ω K M S' R' T' W' z s hstd hdisc hμ' hne hnconn

theorem c26_13_of_facts [Fact AlphaFrame3] (hV : T8YY.LayerFrattiniFact) (hP : T8YY.PureBCase) :
    C26_13 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ
  by_cases hcomp : dComp Ω K = dstarComp Ω K
  · exact T8X.false_of_dComp_eq hs hdisc hcomp hμ (T8V.c27_Ysmall_of_e4sec e4SecNoRoot3)
  · have hB : T8X.W2CaseB3 := T8YY.w2caseB_of_facts hV hP
    by_cases hconn : DConnected (Q3T7.layerFam3 Ω (z * t))
    · exact T8YY.w2caseA3_of_caseB3 hB G Ω K J S R T W z t hs hdisc hμ hcomp hconn
    · exact hB G Ω K J S R T W z t hs hdisc hμ hcomp hconn

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
