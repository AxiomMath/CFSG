module

public import CFSG.Assembly.E6FourNeighbourFacts
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.Assembly.StandardTypeRecognitionDefs

public section

namespace CFSG.Assembly

open CFSG.Blueprint CFSG.StandardType


theorem e6FourSubcompMark_of_psl6 {X : Type} [Group X] (hX : commutator X = ⊤)
    (h : LieModel (X ⧸ Subgroup.center X) .PSL 6 2 2) : E6FourSubcompMark X := by
  have h1 := Canonical.largeEvenMarking_of_lieModel_centerQuot hX h
  refine Canonical.largeEvenMarking_mono ?_ h1
  intro lab R _ I F θ hlab
  obtain ⟨ht, hr, -, hd⟩ := hlab
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp [markTag, markRank, markDeg] at ht hr hd ⊢ <;>
    (try split_ifs at ht hr hd) <;> first | omega | (exfalso; simp_all) | simp_all

theorem e6FourSubcompMark_of_pomegaMinus4 {X : Type} [Group X] (hX : commutator X = ⊤)
    (h : LieModel (X ⧸ Subgroup.center X) .POmegaMinus 4 2 2) : E6FourSubcompMark X := by
  have h1 := Canonical.largeEvenMarking_of_lieModel_centerQuot hX h
  refine Canonical.largeEvenMarking_mono ?_ h1
  intro lab R _ I F θ hlab
  obtain ⟨ht, hr, -, hd⟩ := hlab
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp [markTag, markRank, markDeg] at ht hr hd ⊢ <;>
    (try split_ifs at ht hr hd) <;> first | omega | (exfalso; simp_all) | simp_all

end CFSG.Assembly

end
