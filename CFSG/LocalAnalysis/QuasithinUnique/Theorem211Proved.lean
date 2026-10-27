module

public import CFSG.LocalAnalysis.QuasithinUnique.TopNative

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem theorem_2_1_1_proved :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G :=
  fun _ _ _ _ _ h => theorem_2_1_1_of_branches benderBranch constrainedBranch_proved
    unconstrainedBranch_proved h

end CFSG.QuasithinUnique
