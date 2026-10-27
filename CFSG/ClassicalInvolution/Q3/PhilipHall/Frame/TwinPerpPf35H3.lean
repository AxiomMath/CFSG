module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf34Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf17Perp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf16Local
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelSp62
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelD42
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinModelM12

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q8P.Asc77
open CFSG.ClassicalInvolution.Q8P

theorem twinPerp24S_of_h3 {n : ℕ} (hE : TwinThmE.EIHAll n) (h4 : Thm4RTwinBelow 3 n)
    (h3 : S24B.H3) : TwinPerp24S n :=
  twinPerp24S_of_9coreL hE
    (hyp51TwinInnerPerp_of_model TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert
      TwinCentRes.modelFactM12_of_certs h4)
    (S24B.c24_9_core_of_h3 h3)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
