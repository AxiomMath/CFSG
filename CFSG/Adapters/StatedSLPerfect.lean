module

public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem isPerfect_statedSL_of_three_le {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K] :
    Group.IsPerfect (StatedSL n K) :=
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn
  Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL n K).toMonoidHom)
    (specialLinearGroupEquivStatedSL n K).surjective

theorem isPerfect_statedSL_two_of_four_le_card {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    Group.IsPerfect (StatedSL 2 K) :=
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 2 K).toMonoidHom)
    (specialLinearGroupEquivStatedSL 2 K).surjective

end CFSG.Open.StatedAPI
