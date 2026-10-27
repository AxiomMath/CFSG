module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Elem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Perp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.FiveA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.Fig14
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixAInter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixADerived
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixAOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GraphLocal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem lines_of_hyps (hU : U35Facts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hCube : Vert CubeFacts a z)
    (hPic : Vert A8Pictures a z) (hT4 : Vert TableIVFacts a z) (_hPerp : Vert PerpFacts a z)
    (hT5 : Vert TableVFacts a z) (h6A : Vert SixAFacts a z) (hT7 : Vert TableVIIFacts a z)
    (hPar : Vert ParityFacts a z) : LinesFacts a z := by
  have hnc : ¬ IsConj a z := sixA_not_isConj hT5.self
  have hcom : ∀ x y t : G, IsConj a x → IsConj a y → IsConj a (x * y) → t ≠ x * y →
      t ∈ orb2A a x ∩ orb2A a y → (orb2A a x ∩ orb2A a y ∩ orb2A a t).Nonempty :=
    fun _ _ _ hx hy hxy htxy ht => lines_common h hnc hF3 hPic hx hy hxy htxy ht
  exact
    { six_A := fun _ hx =>
        ⟨lines_sixA_derived h hnc hF3.self hPic.self hT5.self h6A.self hx,
          lines_isShapeA5_derivedOf (hT5.self.shape_6A _ hx),
          fun φ => lines_sixA_orbit h hnc hF3.self hPic.self hT5.self h6A.self hx φ,
          lines_sixA_inter h hx⟩
      five_A := fun _ hx => lines_five_A hU h hnc hPar.self hT4.self hT5 hT7.self hx
      common := hcom
      unique_third := fun _ _ hx hy hxy => lines_unique_third h hCube.self hcom hx hy hxy
      fig14_a := fun _ hx _ hc => lines_fig14_a h hnc hF3 hPic hx hc
      fig14_b := fun _ hx _ ht => lines_fig14_b h hnc hF3 hPic hx ht }

end CFSG.EvenSporadicStandard.HNRecog.Section3
