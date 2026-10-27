module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SDefs
public import CFSG.ClassicalInvolution.Q3.Q3VF4SPartTwin
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem f4PartnerFact3 : F4PartnerFact3 := by
  have hadm : StatedLieAdmissible .POmegaOdd 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by norm_num⟩
  have hsc := ModelFacts.fundamentalSingleClass .POmegaOdd 4 3 1 Nat.prime_three trivial hadm
    (by decide) (by decide)
  have hpow := (Q3W.powCop3_model (t := .POmegaOdd) (n := 4) trivial hadm (by decide)
    (by decide)).pow3
  have hnc := RouteD.Gaps.fundNoncentral 3 .POmegaOdd 4 1 trivial hadm (by decide)
  intro R hR R' hR' hne hcomm hant
  exact twin_partner_spin_odd3 (by norm_num) Q3W.odd_gf3 hsc hpow
    (ModelFacts.OrthAut.odd_hker2 Q3W.two_ne_zero_gf3 4) hnc hR hR' hne hcomm hant

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
