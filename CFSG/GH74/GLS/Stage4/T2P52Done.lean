module

public import CFSG.GH74.GLS.Stage4.T2LeafO
public import CFSG.GH74.GLS.Stage4.T2SL3C
public import CFSG.GH74.GLS.Stage4.T2SL5
public import CFSG.GH74.GLS.Stage4.T2SL3O
public import CFSG.GH74.GLS.Stage4.T2LeafC

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem ch6T2P52
    : Ch6T2P52 :=
  ch6T2P52_of_leaves (ch6T2OddCent_of t2_oc5 t2_oc3) (ch6T2FComm_of t2_c3) (ch6T2FNormX_of t2_c3)

end CFSG.GH74.GLS.Stage4.Rest
