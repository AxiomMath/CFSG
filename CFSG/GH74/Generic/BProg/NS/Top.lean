module

public import CFSG.GH74.Generic.BProg.NS.Lxy
public import CFSG.GH74.Generic.S3.BFreeNbr
public import CFSG.GH74.Generic.S3.BFreeNbhd
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.L5U5 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.E2 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem s_shapeCase_S3_top19_liftJ2NS
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hG : GenericKnownFacts) (hE : E2ComponentFacts) (hFR : L3FRank)
    (hL1 : B_Gen4_liftJ2NS) (hTab : B_S3_pumpupStep) (hN : B_S3_nbrComp)
    (hOnly : B_S3_onlyInvJNT) (hLy : B_S3_LyJNT) (hLxy : B_S3_LxyJNT) :
    S_shapeCaseMaxNT @ShapeS3 := by
  intro G _ _ hs hn hr hgen hK hnab hL x hx K hKc hG2 ⟨hthin, hmax, hsh⟩
  have hset : S3Setup G x K := ⟨hs, hn, hr, hgen, hK, hnab, hL, hx, hKc, hG2, hsh⟩
  have honly : OnlyInvX x K := hOnly G x K hset hmax hthin
  have hT : LiftCentralAt x K := liftCentralAt_of_isJMaxNS hL1 hTab hset hmax hthin
  have hV : LxyLiftAt x K := lxyLiftAt_of_liftJ2NS hG hE hFR hL1 hTab hset hmax hthin
  exact (false_of_onlyInvX_at hGA hset
    (nbhdR_at_of_nbr_at' hGA hset honly hT (hN G x K hset hmax hthin honly) hV
      (hLy G x K hset hmax hthin honly) (hLxy G x K hset hmax hthin honly))).elim

theorem s_shapeCase_S3_top20_liftJ2NS
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hG : GenericKnownFacts) (hE : E2ComponentFacts) (hFR : L3FRank)
    (hL1 : B_Gen4_liftJ2NS) (hTab : B_S3_pumpupStep) (hN : B_S3_nbrComp)
    (hLy : B_S3_LyJNT) (hShape : B_S3_LxyShapeJNT) :
    S_shapeCaseMaxNT @ShapeS3 :=
  s_shapeCase_S3_top19_liftJ2NS hGA hG hE hFR hL1 hTab hN (b_S3_onlyInvJNT_of_liftJ2NS hL1 hTab) hLy
    (b_S3_LxyJNT_of_parts hG hE hLy (b_S3_onlyInvJNT_of_liftJ2NS hL1 hTab)
      (b_S3_nontrivJNT_of_nbrComp hN) hShape hFR)

end CFSG.GH74.Generic.BProg
