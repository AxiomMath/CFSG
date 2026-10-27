module

public import CFSG.GH74.GLS.C3.Layer1.BkGen4L34

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1 Subgroup

variable {G : Type} [Group G]

theorem false_of_isL34Quotient [Finite G]
    (hgen : Gen4 G) {e : G} (he : orderOf e = 2) {H : Subgroup G}
    (hH : IsPCompIn 2 (centralizer ({e} : Set G)) H) (hL : IsL34Quotient (kBar H)) : False := by
  by_cases hZ : center (kBar H) = ⊥
  · exact Bk.false_of_l34_trivial_center hgen he hH hL hZ
  · have hO : pPrimeCore 2 (kBar H) = ⊥ := pPrimeCore_quotient_eq_bot ↥H
    have hZ2 : IsPGroup 2 ↥(center (kBar H)) :=
      (isPGroup_two_center_of_subnormal hO (Subgroup.IsSubnormal.top)).of_equiv
        (Subgroup.centerCongr Subgroup.topEquiv)
    exact Stage1.Main.l34_cover_any (kBar H) (TwoThin.isQuasisimple_hat hH) hZ2 hL hZ
      (Gen4.quotient (pPrimeCore 2 ↥H) (Gen4.subgroup H hgen))

end CFSG.GH74.Generic.BProg.B3
