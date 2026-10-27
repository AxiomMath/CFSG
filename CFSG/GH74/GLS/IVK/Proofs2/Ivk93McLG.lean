module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovProved

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P34

theorem ivk93Kind_mcl
    : Ivk93Kind Kind.mcl :=
  ivk93Kind_sporadic_of ivk93CovJ_proved ivk93cov_oneClass_proved (Or.inl rfl)

end CFSG.GH74.GLS.IVK.Proofs2
