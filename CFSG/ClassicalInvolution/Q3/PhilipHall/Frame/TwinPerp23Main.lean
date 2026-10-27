module

public import CFSG.ClassicalInvolution.Asc77.AscT7BAlpha
public import CFSG.ClassicalInvolution.AschTight.S19TStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform

section Alpha

variable {Y : Type} [Group Y]

theorem gamma2_le_normalizer_alphaOf {B α₀ : Subgroup Y}
    (h : ∀ A : Subgroup Y, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀) (H : Subgroup Y) :
    gamma2 B H ≤ Subgroup.normalizer (α₀ : Set Y) := by
  refine iSup₂_le fun A hA => ?_
  have hA' : A ≤ B ∧ IsElemAbelian2 A 2 := hA
  calc H ⊓ Subgroup.centralizer (A : Set Y) ≤ Subgroup.centralizer (A : Set Y) := inf_le_right
    _ ≤ Subgroup.normalizer (alphaOf A : Set Y) := T7B.centralizer_le_normalizer_alphaOf A
    _ = Subgroup.normalizer (α₀ : Set Y) := by rw [h A hA'.1 hA'.2]

theorem eq_bot_of_normal_odd {A : Subgroup Y} (hO : classicalInvolutionOddCore Y = ⊥)
    (hN : A.Normal) (hodd : Odd (Nat.card A)) : A = ⊥ := by
  have hle : A ≤ classicalInvolutionOddCore Y := le_sSup ⟨hN, hodd⟩
  rw [hO] at hle
  exact le_bot_iff.mp hle

theorem alpha_eq_bot_of_gamma {B : Subgroup Y} {u z : Y}
    (hO : classicalInvolutionOddCore Y = ⊥)
    (hT : Subgroup.centralizer ({u} : Set Y) ⊔ Subgroup.centralizer ({z} : Set Y) = ⊤)
    (hΓz : Subgroup.centralizer ({z} : Set Y) ≤ gamma2 B (Subgroup.centralizer ({z} : Set Y)))
    (hΓu : Subgroup.centralizer ({u} : Set Y) ≤ gamma2 B (Subgroup.centralizer ({u} : Set Y)))
    (hodd : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, z} : Set Y)))))
    (halpha : ∀ A : Subgroup Y, A ≤ B → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set Y))) :
    alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ := by
  have hN : Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set Y)) : Set Y) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hT]
    exact sup_le (hΓu.trans (gamma2_le_normalizer_alphaOf halpha _))
      (hΓz.trans (gamma2_le_normalizer_alphaOf halpha _))
  exact eq_bot_of_normal_odd hO (Subgroup.normalizer_eq_top_iff.mp hN) hodd

end Alpha

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
