module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagLift
import CFSG.ClassicalInvolution.Phan.PhanDn.DiameterQTwo
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves
import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoTriangleSolid

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

private theorem cycleHomotopic_triWalk_of_flipColl [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 3 ≤ m)
    {u x y : FlipPt σ (m + 1)} (h₁ : (flipGraph σ (m + 1)).Adj u x)
    (h₂ : (flipGraph σ (m + 1)).Adj x y) (h₃ : (flipGraph σ (m + 1)).Adj y u) :
    CycleHomotopic (flagNullWalks σ hm) (triWalk h₁ h₂ h₃) .nil := by
  have hU : IsFlipflopSub σ ((u.1 ⊔ x.1) ⊔ y.1) :=
    isFlipflopSub_sup_of_flipColl_triangle hσ hK u.2 x.2 y.2 h₁ h₂ h₃
  refine cycleHomotopic_of_mem (flagNullWalks σ hm)
    (solidWalks_subset_flagNullWalks hm u ?_)
  refine mem_solidWalks_of_le (n := m + 1) hσ hU ?_
  intro z hz
  simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact le_trans le_sup_left le_sup_left
  · exact le_trans le_sup_right le_sup_left
  · exact le_sup_right
  · exact le_trans le_sup_left le_sup_left

theorem nullLen_three_flagNullWalks_of_card_eq_four [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 3 ≤ m) :
    NullLen (flagNullWalks σ hm) 3 := by
  intro u p hp
  match u, p, hp with
  | _, .cons h₁ (.cons h₂ (.cons h₃ .nil)), _ =>
    exact cycleHomotopic_triWalk_of_flipColl hσ hK hm h₁ h₂ h₃
  | _, .nil, hp => simp at hp
  | _, .cons _ .nil, hp => simp at hp
  | _, .cons _ (.cons _ .nil), hp => simp at hp
  | _, .cons _ (.cons _ (.cons _ (.cons _ _))), hp =>
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

theorem flagGraph_connected_of_card_eq_four (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    (hm : 4 ≤ m) : (flagGraph σ m).Connected :=
  connected_flagGraph hσ (Nat.le_of_succ_le hm)
    (flipGraph_connected_of_card_eq_four hσ hK (by omega))

theorem triangulable_flagGraph_of_card_eq_four_of_nullLen [Finite K] [CharP K 2]
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4) (hm : 4 ≤ m)
    (h4 : NullLen (flagNullWalks σ (Nat.le_of_succ_le hm)) 4)
    (h5 : NullLen (flagNullWalks σ (Nat.le_of_succ_le hm)) 5) :
    CFSG.Monster.B.Recog.Triangulable (flagGraph σ m) := by
  have hm3 : 3 ≤ m := Nat.le_of_succ_le hm
  have hconn : (flipGraph σ (m + 1)).Connected :=
    flipGraph_connected_of_card_eq_four hσ hK (by omega)
  refine triangulable_flagGraph hσ hm3 hconn ?_
  exact cycleTrivial_of_nullLen (flagNullWalks σ hm3) hconn
    (flipGraph_ediam_le_two_of_card_eq_four hσ hK (by omega))
    (nullLen_three_flagNullWalks_of_card_eq_four hσ hK hm3) h4 h5

end CFSG.ClassicalInvolution.PhanDn
