module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFooteBridge
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolMirror
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSkeleton
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

theorem mem_footeFamilyOf_of_gsMirrorReach {G : Type} [Group G] [Finite G] {L A V : Subgroup G}
    {w : G} (hAF : A ∈ footeFamilyOf L) (hML : GSMirrorMaximal A) (hw : orderOf w = 2)
    (hV : IsTwoComponentIn V (centralizer ({w} : Set G))) (hAV : GSMirrorReach A V) :
    V ∈ footeFamilyOf L := by
  obtain ⟨eAV⟩ := hML V hAV
  obtain ⟨-, ⟨eAL⟩⟩ := hAF
  refine ⟨⟨w, ⟨hw, hV.1, hV.2⟩, fun b X hX => ?_⟩, ⟨eAV.symm.trans eAL⟩⟩
  obtain ⟨eAX⟩ := hML X (Relation.ReflTransGen.trans hAV
    (GSMirrorReach.of_weakReach (GrSLit.gsWeakReach_of_footeReach hX.footeReach)))
  exact ⟨eAV.symm.trans eAX⟩

end CFSG.ComponentClassification.FooteLit
