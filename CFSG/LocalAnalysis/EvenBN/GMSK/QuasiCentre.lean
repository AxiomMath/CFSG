module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreStatement
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreTransfer
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreLayer
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreCatalog
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreAlt
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreOdd
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreEven
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadic

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

section Certified


theorem qFixedRootSelector_all : QFixedRootSelector fun D _ => Catalog D :=
  qFixedRootSelector_catalog qFixedRootSelector_alternating qFixedRootSelector_oddLieType
    qFixedRootSelector_evenLieType qFixedRootSelector_sporadic

theorem gmsUnitaryCentre : GMSUnitaryCentreStatement := by
  intro H _ _ hK n J t hJq hJm ht htJ hJn hrank hnn
  set R := CFSG.Open.standardComponentOddCore H with hRdef
  have hR : Odd (Nat.card R) := odd_card_standardComponentOddCore H
  obtain ⟨hq, hm, hθt, hθJ, hN, hrk, hZ⟩ := quasi_transfer hJq hJm ht htJ hJn hrank R hR
  have hK' : CFSG.SectionRank.IsKGroupCat (H ⧸ R) := hK.quotient R
  have hO : CFSG.Open.standardComponentOddCore (H ⧸ R) = ⊥ :=
    standardComponentOddCore_quotient_eq_bot H
  refine hZ ?_
  rcases quasi_layer_dichotomy hK' hO hq hθt hθJ hN hrk hnn with
    hc | ⟨L, hLs, α, hcat, hJL, hα, hle, hnorm, hr⟩
  · exact hc
  · set J' := J.map (QuotientGroup.mk' R) with hJ'
    let e : ↥(J'.subgroupOf L) ≃* ↥J' := Subgroup.subgroupOfEquivOfLe hJL
    have hq' : CFSG.Open.IsQuasisimple ↥(J'.subgroupOf L) :=
      isQuasisimple_open_of_mulEquiv e.symm hq
    have hm' : LieModel (↥(J'.subgroupOf L) ⧸ center ↥(J'.subgroupOf L)) .PSU 3 2 n :=
      lieModel_quotient_center_of_mulEquiv e.symm hm
    have d : QFixedRootDatum ↥L n α (J'.subgroupOf L) := ⟨hα, hle, hnorm, hq', hm', hr⟩
    exact center_eq_bot_of_mulEquiv_aux e (qFixedRootSelector_all ↥L hLs hcat n α _ d)

end Certified

end CFSG.LocalAnalysis.EvenBN.GMSK
