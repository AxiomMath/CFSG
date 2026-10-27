module

public import CFSG.CGT.M24S.NSHolt
public import CFSG.CGT.M24S.NSMho4

public section

namespace CFSG.CGT.M24S

theorem hasComplement_of_hyp {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hHolt : CFSG.Holt.H78.HoltTheorem1) {T H : Subgroup G} (h : Hyp T H)
    (hL : LocalFacts T H) (hC : Subgroup.centralizer (T : Set G) = T) : HasComplement T H :=
  hasComplement_of_hyp_of_ns5 hHolt h hL hC
    (fun hns _x hxH hxT hx2 => exists_sylow_sqDerivedEq h.le h.nat hns hxH hxT hx2)

end CFSG.CGT.M24S
