module

public import CFSG.ClassicalInvolution.Q3.Quasisimple
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts

theorem partOneSolvable_of_connectedBranch3 (h : ConnectedBranch3) (hM : M11Facts) :
    PartOneSolvable :=
  partOneSolvable_of_cit3Inductive (cit3Inductive_of_connectedBranch h) modelClauseZero hM

theorem normalOddByQuaternionLarge_of_connectedBranch3 (h : ConnectedBranch3) (hM : M11Facts)
    (hlift : TightLift3) : NormalOddByQuaternionLarge :=
  normalOddByQuaternionLarge_of_cit3Inductive (cit3Inductive_of_connectedBranch h) modelClauseZero
    hM hlift

theorem partOneSolvable_of_parts (hS : SolvableConnected3) (hQ : QuasisimpleConnected3)
    (hcore : CoreStep3) (hfund : ClassicalIsFundamental3) (hcl : CentralLift 3)
    (hM11 : M11Branch3) (hM : M11Facts) : PartOneSolvable :=
  partOneSolvable_of_connectedBranch3 (connectedBranch3_of_parts hS hQ hcore hfund hcl hM11) hM

theorem normalOddByQuaternionLarge_of_parts (hS : SolvableConnected3) (hQ : QuasisimpleConnected3)
    (hcore : CoreStep3) (hfund : ClassicalIsFundamental3) (hcl : CentralLift 3)
    (hM11 : M11Branch3) (hM : M11Facts) (hlift : TightLift3) : NormalOddByQuaternionLarge :=
  normalOddByQuaternionLarge_of_connectedBranch3
    (connectedBranch3_of_parts hS hQ hcore hfund hcl hM11) hM hlift

end CFSG.ClassicalInvolution.Q3
