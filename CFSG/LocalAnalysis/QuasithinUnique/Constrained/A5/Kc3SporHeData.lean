module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporHeCertificateInputs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.He.Action

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporHeChk

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat.He
  CFSG.QuasithinUnique.A5.Kc3SporPerm

noncomputable instance heAct
    : MulAction CFSG.Sporadic.He.J (Fin hePD.n) :=
  CFSG.Sporadic.He.idxInst

end CFSG.QuasithinUnique.A5.Kc3SporHeChk
