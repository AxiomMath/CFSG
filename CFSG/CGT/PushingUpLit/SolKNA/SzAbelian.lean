module

public import CFSG.CGT.PushingUpLit.SolKNA.SzExtract
public import CFSG.CGT.PushingUpLit.SolKNA.SzModelFacts
import all CFSG.CGT.PushingUpLit.SolKNA.Lemma18Amb
public import CFSG.CGT.PushingUpLit.SolKNA.Lemma18Amb

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

theorem lemma18SzAbelian_of_weight (hW : SzCommutatorWeight) :
    Lemma18SzAbelian :=
  lemma18SzAbelian_of_facts hW rootSz_zero_mul rootSz_mul_zero_comm torus_conj_root_zero
    (fun ha E hc hsq hcard => exists_conj_eq_Z ha E hc hsq hcard)

end CFSG.CGT.PushingUpLit.SolKNA
