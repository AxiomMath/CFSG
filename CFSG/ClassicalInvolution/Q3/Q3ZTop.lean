module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjFinal
public import CFSG.ClassicalInvolution.Q3.Q3ZClose
public import CFSG.ClassicalInvolution.Q3.Q3ZFrbFrame
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3TMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic


theorem piece3Sp2_of_chainInput (h3 : Q3W.OddThreeFreeInput) (hchain : C3ChainInput)
    (hU : V6Universal) (hC : V6Collapse) : Q3W.Piece3Sp2 := by
  rintro a t n ⟨rfl, rfl, rfl⟩ G _ _ _ hnab K z hR hshape
  have hO3 : Q3W.LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  obtain ⟨U, hU2, hcomm, hA, hB⟩ := hchain G hnab K z hR hshape hO3
  obtain ⟨Ψ, hker, hlong⟩ := weakCT3_symplectic_chain hU hC U hcomm hA hB
  exact Or.inl (oddLieType_of_psi_psp3 hnab hR hshape hO3 Ψ hker (hlong ▸ hU2))

theorem piece3Sp2_of_a2rel (h3 : Q3W.OddThreeFreeInput) (hA : C3A2Rel) (hU : V6Universal)
    (hC : V6Collapse) : Q3W.Piece3Sp2 :=
  piece3Sp2_of_chainInput h3 (c3ChainInput_of_a2rel hA) hU hC

@[expose] def TypeC3Shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K → Setup3 K z →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K →
      Q3W.LocalShapeC3 1 (CompData.model .PSp 2) (conjClass3 K) z

theorem typeC3Rec_of_shape (hshape : TypeC3Shape) (hrow : Q3W.Piece3Sp2) : TypeC3Rec := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 hS hint
  have hR := Q3W.RouteD3Setup.of_hyps hz hBelow h3 h4 hΔ hS hint
  exact hrow 1 .PSp 2 ⟨rfl, rfl, rfl⟩ G hnab K z hR
    (hshape G hnab K z hz hBelow h3 h4 hΔ hB hA2 hS hint)

theorem typeC3Rec_of_inputs (hshape : TypeC3Shape) (h3 : Q3W.OddThreeFreeInput)
    (hA : C3A2Rel) (hV : V6Check) (hVC : V6CollapseCheck) : TypeC3Rec :=
  typeC3Rec_of_shape hshape
    (piece3Sp2_of_a2rel h3 hA (v6Universal_of_check hV) (v6Collapse_of_check hVC))

end CFSG.ClassicalInvolution.Q3.Q3Z
