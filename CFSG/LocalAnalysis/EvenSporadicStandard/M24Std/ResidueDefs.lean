module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputThird
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def HasElemAbThree81 (X : Type*) [Group X] : Prop :=
  ∃ S : Subgroup X, Nat.card S = 81 ∧ (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) ∧ ∀ s ∈ S, s ^ 3 = 1

@[expose] def Ega81Sit
    (P : (G : Type) → [Group G] → [Finite G] → Subgroup G → G → Subgroup G → Subgroup G →
      Subgroup G → Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G),
    fusionZStar G = ⊥ → standardComponentIsStandard L → LocalSetting G L z →
    ∀ A B C D : Subgroup G, FirstHalfData L z A B C D → P G L z A B C D

structure Ega81Residue : Prop where
  cA6 : Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃* alternatingGroup (Fin 6)) → False
  cA8 : Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃* alternatingGroup (Fin 8)) → False
  cU42 : Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSU 4 2 1 → False
  cL52 : Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSL 5 2 1 → False
  cU52 : Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSU 5 2 1 → False
  cSp44 : Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSp 2 2 2 → False
  cU43 : Ega81Sit fun _ _ _ _ _ _ _ C _ =>
    LieModel (egaLayer (egQD C ⧸ fusionOddCore (egQD C))) .PSU 4 3 1 → False
  cStruct : Ega81Sit fun _ _ _ _ _ _ _ C D =>
    Nonempty (egaLayer (egQD C ⧸ fusionOddCore (egQD C)) ≃*
      alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) →
    HasElemAbThree81 (egQD D ⧸ fusionOddCore (egQD D))
  dPos : Ega81Sit fun _ _ _ _ z _ _ _ D =>
    Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃*
      alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) → FFzData D z

end CFSG.EvenSporadicStandard.M24Std
