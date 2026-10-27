module

public import Certificates.Certificate26772

public section

namespace CFSG.EvenSporadicStandard.HNRecog

section Cert


theorem tableI1OK_true : tableI1OK = true := Certificates.certificate26772.1

theorem tableI3OK_true : tableI3OK = true := Certificates.certificate26772.2.1

theorem tableI2_shape
    (hX : Nat.card ↥(Subgroup.closure (elemW '' {w | w ∈ blkData2.gens})) = 80640)
    (hXeq : Subgroup.closure (elemW '' {w | w ∈ blkData2.gens}) =
      P1408 ⊓ Subgroup.centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) :
    IsShapeTwoTwoTimesA8 ↥(Subgroup.closure (elemW '' {w | w ∈ blkData2.gens})) :=
  Certificates.certificate26772.2.2 hX hXeq

end Cert

end CFSG.EvenSporadicStandard.HNRecog
