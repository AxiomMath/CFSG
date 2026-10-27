module

public import CFSG.CGT.PushingUpLit.SolKNA.SzAbelian
public import CFSG.CGT.PushingUpLit.SolKNA.SzWeight
public import CFSG.RankThree.GF2n.Tim77Prop24TwoSz

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.RankThree.GF2n (MartineauSzInput)

theorem lemma18SzAbelian_of_simple (h : SzFpfSimpleNatural) :
    Lemma18SzAbelian :=
  lemma18SzAbelian_of_weight (szCommutatorWeight_of_simple h)

end CFSG.CGT.PushingUpLit.SolKNA
