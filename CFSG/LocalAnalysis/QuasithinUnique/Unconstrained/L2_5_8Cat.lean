module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8A6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2pB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8M11
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate110
public import Certificates.Certificate2191
public import Certificates.Certificate3120
public import Certificates.Certificate4041
public import Certificates.Certificate4048
public import Certificates.Certificate4145
public import Certificates.Certificate4154
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsNormal

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem smallListCatalogue
    : SmallListCatalogue :=
  { a6 := fun X _ _ hm => Unc25A6.a6_facts X hm
    l32 := fun X _ _ hm => Unc25Small.l32_facts X hm
    l33 := fun X _ _ hm => Unc25L33.l33_facts X hm
    m11 := fun X _ _ hm => Unc25M11.m11_facts X hm
    l2p := fun _ hFM h7 X _ _ hm => Unc25Small.l2p_facts hFM h7 X hm }

theorem lemma258_proved
    : Lemma258 := lemma258 smallListCatalogue

end CFSG.QuasithinUnique
