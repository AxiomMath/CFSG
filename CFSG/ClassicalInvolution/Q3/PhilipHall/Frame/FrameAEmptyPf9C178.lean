module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem nonempty_equiv_q8 {M : Subgroup G} (h : IsQuatSub M) (h8 : Nat.card M = 8) :
    Nonempty (↥M ≃* QuaternionGroup 2) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := h
  have hc : Nat.card M = 4 * 2 ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : 2 ^ k = 2 ^ 1 := by omega
  have hk1 : k = 1 := Nat.pow_right_injective (le_refl 2) h2
  subst hk1
  exact ⟨e⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
