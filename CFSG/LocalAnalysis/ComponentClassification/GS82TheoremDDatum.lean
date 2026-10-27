module

public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import CFSG.GH74.GLS.TwoThin.Orbit
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.TheoremD

open CFSG Subgroup GH74.GLS GH74.GLS.TwoThin Equiv Equiv.Perm RankThree.PerfectCover
open scoped MatrixGroups

theorem nonempty_psl_two_five_equiv :
    Nonempty
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5) ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
  have hSL : Nat.card SL(2, ZMod 5) = 120 := by
    rw [Matrix.card_SL_field (𝔽 := ZMod 5) 2, ZMod.card, Fin.prod_univ_two]
    norm_num
  have hZ : Nat.card (center SL(2, ZMod 5)) = 2 := by
    rw [OrderReductions.LinearOrders.card_specialLinear_center (ZMod 5) 2 (by norm_num),
      Nat.card_zmod]
    norm_num
  have h60 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = 60 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(2, ZMod 5))
    rw [hZ, hSL] at h
    change 120 = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) * 2 at h
    omega
  exact QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60

end CFSG.ComponentClassification.GS82PumpInputs.TheoremD
