module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel
public import Certificates.Certificate320030

public section

namespace CFSG.GH74.QTGen4.DSGen4

theorem a5Facts : Certificates.A5GL42.Facts :=
  Certificates.certificate320030

theorem A5Pre.exists_model' {G : Type} [Group G] [Finite G]
    {P L E K : Subgroup G} (h : A5Pre P L E K) :
    (NatSec L K E ∧ Nonempty (A5Model P L E K Certificates.A5GL42.HN)) ∨
      (¬ NatSec L K E ∧ Nonempty (A5Model P L E K Certificates.A5GL42.HO)) :=
  h.exists_model a5Facts

end CFSG.GH74.QTGen4.DSGen4
