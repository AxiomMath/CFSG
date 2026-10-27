module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Three
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.CentQ

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGz_of_hyps (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (_hOrb : Vert GzOrbitFacts a z)
    (hCls : Vert GzClassFacts a z) (_hY4a : Vert Y4aFacts a z) (hGz9 : Vert Gz9Facts a z) :
    StructGzFacts a z :=
  have hA := structGz_aschbacherHyp_pCore hGz9.self
  { three := structGz_three hC h (structGz_cIrreducible_of_aschbacherHyp hA)
    five := structGz_five hC h hA
    centQ_inv := structGz_centQ_inv hC h hA
    y4b := fun _ ha₁ ha₁A ha₁z =>
      (y4a_struct_of_good hI h hF1 hF2 hF3 hPic hCls.self ha₁ ha₁A ha₁z).2 }

end CFSG.EvenSporadicStandard.HNRecog.Section3
