module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagLift
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
import CFSG.ClassicalInvolution.Phan.PhanDn.FlagQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.ConeHighQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.ConeFiveQTwo
import CFSG.ClassicalInvolution.Phan.PhanDn.PentQTwo

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

theorem nullLen_four_flagNullWalks_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 4 ≤ m) :
    NullLen (flagNullWalks σ (Nat.le_of_succ_le hm)) 4 := by
  refine nullLen_four_flagNullWalks_of_coneConnected hσ hK (Nat.le_of_succ_le hm) ?_
  by_cases h5 : 5 ≤ m
  · intro a c _ _
    exact coneConnected_of_card_eq_four hσ hK h5 a c
  · obtain rfl : m = 4 := by omega
    intro a c hac hadj
    by_cases hc : c.1 = dFlipSub σ a.1
    · exact coneConnected_dFlipSub_of_card_eq_four hσ hK le_rfl a c hc
    · exact coneConnected_five_of_card_eq_four hσ hK a c hac hadj hc

theorem flagGraph_connected_triangulable_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 4 ≤ m) :
    (flagGraph σ m).Connected ∧ CFSG.Monster.B.Recog.Triangulable (flagGraph σ m) :=
  ⟨flagGraph_connected_of_card_eq_four hσ hK hm,
    triangulable_flagGraph_of_card_eq_four_of_nullLen hσ hK hm
      (nullLen_four_flagNullWalks_of_card_eq_four hσ hK hm)
      (nullLen_five_flagNullWalks_of_card_eq_four hσ hK hm
        (nullLen_four_flagNullWalks_of_card_eq_four hσ hK hm))⟩

end CFSG.ClassicalInvolution.PhanDn
