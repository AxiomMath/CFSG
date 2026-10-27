module

public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinConj
public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinGen
public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniConj
public import CFSG.GH74.GLS.IVK.Proofs2.Std44UniGen

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK

theorem ivk_4_4a : IVK_4_4a :=
  ivk_4_4a_of_targets (fun F _ _ h => linConj F h) (fun F _ _ h => linGen F h)
    (fun F _ _ _ hq hF => uniConj F hq hF) (fun F _ _ _ hq hF => uniGen F hq hF)

end CFSG.GH74.GLS.IVK.Proofs2
