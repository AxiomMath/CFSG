module

public import CFSG.ClassicalInvolution.Q3.Main
public import CFSG.ClassicalInvolution.Q3.M11Branch
public import CFSG.ClassicalInvolution.Q3.SP3
import CFSG.ClassicalInvolution.ModelFacts.CentralLiftE6

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic

theorem partOneSolvable_of_remaining (hQ : QuasisimpleConnected3) (hcore : CoreStep3)
    (hfund : ClassicalIsFundamental3) : PartOneSolvable :=
  partOneSolvable_of_parts SP3.solvableConnected3 hQ hcore hfund (ModelFacts.centralLift 3)
    m11Branch3 m11Facts

theorem normalOddByQuaternionLarge_of_remaining (hQ : QuasisimpleConnected3) (hcore : CoreStep3)
    (hfund : ClassicalIsFundamental3) (hlift : TightLift3) : NormalOddByQuaternionLarge :=
  normalOddByQuaternionLarge_of_parts SP3.solvableConnected3 hQ hcore hfund
    (ModelFacts.centralLift 3) m11Branch3 m11Facts hlift

end CFSG.ClassicalInvolution.Q3
