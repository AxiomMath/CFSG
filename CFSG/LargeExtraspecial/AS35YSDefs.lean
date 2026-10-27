module

public import CFSG.LargeExtraspecial.AS35YLSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace S14

@[expose] def Asc512FixRadSingStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    InspNondeg _ S.EhatAsc → (∃ m, 4 ≤ m ∧
      (LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL m 2 1 ∨
        LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp m 2 1 ∨
        LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus m 2 1 ∨
        LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus m 2 1)) →
    ∀ v : S.Qt, (∀ l ∈ S.LbarAsc, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) →
      (∀ w : S.Qt, (∀ l ∈ S.LbarAsc, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) →
        polar S.q v w = 0) → S.q v = 0

@[expose] def Asc512U33FixNonsingStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    Asc512U33Fam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc → S.width = 4 →
    ∀ v : S.Qt, (∀ l ∈ S.LbarAsc, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → S.q v = 1 → False

end S14

end CFSG.LargeExtraspecial
