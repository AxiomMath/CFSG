module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32A8Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32B

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem k32ExclA8_of (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) : K32ExclA8 :=
  k32ExclA8_of_index fun _ _ _ _ _ _ _ _ _ _ _ _ hA => (hA.relIndex_baum_sOne' hD h27_1).le

end CFSG.QuasithinUnique.DoubleA3
