module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBWit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBGmat
public import Certificates.Certificate136201
public import Certificates.Certificate136202
public import Certificates.Certificate136203
public import Certificates.Certificate136204
public import Certificates.Certificate136205
public import Certificates.Certificate136206

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
  CFSG.Monster.Existence


theorem twoAPureKlein_three_Gmat : TwoAPureKlein 3 Gmat := by
  have hE := m3bEqs_all
  have hM := m3bMoves_all
  have ht : IsTwoA tGmat := ⟨CFSG.Monster.Tri.orderOf_tGmat, natCard_centralizer_tStar⟩
  have hE' : agreeAll (m3bBaseEqs ++ m3bClassEqs) = true := hE
  obtain ⟨-, -, -, ht3, -⟩ := base_facts (agreeAll_append_iff.1 hE').1
  refine twoAPureKlein_three_of Certificates.certificate136200
    Certificates.certificate136201 Certificates.certificate136202
    (fun k hk => ?_) ht3 (rootGood_of_eqs ht hE hM)
  interval_cases k
  · exact Certificates.certificate136203
  · exact Certificates.certificate136204
  · exact Certificates.certificate136205
  · exact Certificates.certificate136206

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
