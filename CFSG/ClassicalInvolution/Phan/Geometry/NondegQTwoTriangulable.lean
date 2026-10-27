module

public import CFSG.ClassicalInvolution.Phan.Geometry.NondegQTwoPentagons
public import CFSG.ClassicalInvolution.Phan.Geometry.NondegQTwoQuad

public section

namespace CFSG.ClassicalInvolution.Phan

open Module CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Recog

variable {K : Type*} [Field K] {σ : K ≃+* K} {d : ℕ}

theorem ndGraph_triangulable (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {W : Submodule K (Fin d → K)} (hW : Nondeg σ W)
    (h5 : 5 ≤ Module.finrank K W) : Triangulable (ndGraph σ W) := by
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have h3 : NullLen (ndNull (σ := σ) (W := W) (by omega)) 3 := ndNullLen3 hσ hK (W := W) (by omega)
  have h4 : NullLen (ndNull (σ := σ) (W := W) (by omega)) 4 := ndNullLen4 hσ hK hW h5 h3
  apply triangulable_ndGraph_of_cycleTrivial hσ hW h5
  exact cycleTrivial_of_nullLen (ndNull (σ := σ) (W := W) (by omega))
    (collGraph_connected_of_four_le hσ hW (by omega))
    (collGraph_ediam_le_two_of_four_le hσ hW (by omega))
    h3 h4 (ndNullLen5 hσ hK hW h5 h4)

end CFSG.ClassicalInvolution.Phan
