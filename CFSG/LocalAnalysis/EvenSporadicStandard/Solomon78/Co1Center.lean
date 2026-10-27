module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterC

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

theorem centerInvolutions_GA :
    CenterInvolutions GA := by
  refine CenterInvolutions.of_classes [aC, cC, a₁] (fun s hs => ?_) (fun r hr => ?_)
  · rcases involution_classes.1 s hs with h | h | h
    · exact ⟨aC, by simp, h⟩
    · exact ⟨cC, by simp, h⟩
    · exact ⟨a₁, by simp, h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact centerInvAt_aC
    · exact centerInvAt_cC
    · exact centerInvAt_a₁

theorem centerInvolutions_native :
    CenterInvolutions CFSG.Blueprint.NativeSporadic.Co1 :=
  @CenterInvolutions.of_mulEquiv GA CFSG.Blueprint.NativeSporadic.Co1 _ Units.instGroup
    co1MatEquiv.symm centerInvolutions_GA

end CFSG.EvenSporadicStandard.Solomon78
