module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceAdapterCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.Piece

theorem natAdapterProp : NatAdapterProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hloc hres
  classical
  have hS := ctx.setting
  have h2 := hS.two_le
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    exact charP_two_of_card_pow (n := n) (by rw [← Nat.card_eq_fintype_card]; exact hS.card_eq)
  have hbase := hloc.base
  have hbasic := hloc.basic
  have himage := hloc.image
  have hK := hloc.K
  have hcamp := hloc.campbell
  have hSP : baum R ≤ P := hbasic.lt.le
  have hIS : modComm V (Lc i) ≤ baum R := himage.I_le_S
  have hP : P ≤ Subgroup.normalizer (V : Set G) := le_top.trans ctx.hX
  have hBP : oddOrderSubgroup P ≤ P := oddOrderSubgroup_le P
  have hBN : oddOrderSubgroup P ≤ Subgroup.normalizer (V : Set G) := hBP.trans hP
  obtain ⟨hchi, hLin, -, hE, hUK, hcent, -⟩ := adapter_core (k := F) (S := baum R) (P := P)
    (M := M) (W := modComm V (Lc i)) hSP hIS hbase.B_S hres.P_eq hbasic.charTwo hbasic.noChar
    (by omega : 1 ≤ n) hS.card_eq hcamp.setting hcamp.thompson_ne
  have hperf : ⁅autOn (oddOrderSubgroup P) V, autOn (oddOrderSubgroup P) V⁆ =
      autOn (oddOrderSubgroup P) V := by
    rw [hK.image]
    exact Subgroup.isPerfect_iff.mp (Family.isQuasisimple_of_isComp (ctx.comps.isComp i)).1
  have := hS.reduced.2.2.1.1
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hII : ⁅modComm V (Lc i), oddOrderSubgroup P⁆ = modComm V (Lc i) := by
    have e1 : modComm V (Lc i) = ⁅oddOrderSubgroup P, V⁆ := by
      rw [← hK.image]
      exact modComm_autOn hBN
    rw [e1, Subgroup.commutator_comm, commutator_commutator_eq hBN hVcomm hperf]
  refine ⟨hchi, hLin (by omega), ?_, ?_⟩
  · have : blockU (oddOrderSubgroup P) = modComm V (Lc i) := by rw [hUK, hE, hII]
    exact this
  · rw [hE, hII] at hcent
    exact hcent

end CFSG.QuasithinUnique.Setup.Lift
