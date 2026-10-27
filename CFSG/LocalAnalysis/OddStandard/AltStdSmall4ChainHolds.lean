module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ChainW
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4WF9
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusP42
public import CFSG.LocalAnalysis.OddStandard.AltStdEvenP42
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4N0Struct
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G1Holds
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4W49Ident
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Start
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2Frat
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2TermHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerHolds

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup

theorem sec4WreathFalse_of_parts (hB : Sec4WreathFalseBig) :
    Sec4WreathFalse := by
  have h9 := sec4WreathFalseSmall_holds
  intro G _ _ L Q n θ z c T hH hW
  by_cases h : IsASmall L n z
  · exact h9 G L Q n θ z c T h hH hW
  · exact hB G L Q n θ z c T h hH hW

theorem cycTwoInnerSmallFalseE_of_tower
    (hW : Tower.WrFalse)
    (hS : Tower.SlFalse) :
    ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
      (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwoE G L Q n θ z → n ≤ 11 →
        centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) → False :=
  cycTwoInnerSmallFalseE_of_chainW (Fus.sec4FusionN0_of_parts Fus.fusR9 Fus.fusRS9 Fus.fusR11
      Fus.fusJ Fus.fusP42_holds Fus.fusR8 Fus.fusRS8 Fus.fusR10 Fus.fusJ8 Fus.fusP42Eight_holds) sec4N0Struct_holds
    (G2.sec4N0Elementary_of_parts G2.g2Start_holds (G2.g2Step_of_cover G2.stepCover_holds) G2.g2Terminal_holds) sec4HSetup_holds HbarCoords.sec4HbarCases_holds
    sec4HbarNotSmall_holds (Tower.sec4HbarNotSL_of hS) (W49.sec4Wreath49_of_ident
        HbarCoords.sec4HbarIdent_holds)
    (sec4WreathFalse_of_parts (Tower.sec4WreathFalseBig_of hW))

theorem cycTwoShapeTwoSmallFalse_of_tower
    (hW : Tower.WrFalse)
    (hS : Tower.SlFalse) :
    ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
      (θ : L ≃* alternatingGroup (Fin n)) (z u : G), OrderTwoE G L Q n θ z → n ≤ 9 →
        u ∈ centralizer ({z} : Set G) → u ∉ L ⊔ centralizer (L : Set G) → u ^ 2 = 1 → False :=
  cycTwoShapeTwoSmallFalse_of_chainW (Fus.sec4FusionN0_of_parts Fus.fusR9 Fus.fusRS9 Fus.fusR11
      Fus.fusJ Fus.fusP42_holds Fus.fusR8 Fus.fusRS8 Fus.fusR10 Fus.fusJ8 Fus.fusP42Eight_holds) sec4N0Struct_holds
    (G2.sec4N0Elementary_of_parts G2.g2Start_holds (G2.g2Step_of_cover G2.stepCover_holds) G2.g2Terminal_holds) sec4HSetup_holds HbarCoords.sec4HbarCases_holds
    sec4HbarNotSmall_holds (Tower.sec4HbarNotSL_of hS) (W49.sec4Wreath49_of_ident
        HbarCoords.sec4HbarIdent_holds)
    (sec4WreathFalse_of_parts (Tower.sec4WreathFalseBig_of hW))

theorem cycTwoInnerSmallFalse_of_tower
    (hW : Tower.WrFalse)
    (hS : Tower.SlFalse) : AltStdCycTwo.CycTwoInnerSmallFalse := by
  intro G _ _ L Q n θ z hT h11 hin
  exact cycTwoInnerSmallFalseE_of_tower hW hS G L Q n θ z hT.toE h11 hin

theorem cycTwoShapeTwoNineFalse_of_tower
    (hW : Tower.WrFalse)
    (hS : Tower.SlFalse) : AltStdCycTwo.CycTwoShapeTwoNineFalse := by
  intro G _ _ L Q θ z u hT huC huO hu1
  exact cycTwoShapeTwoSmallFalse_of_tower hW hS G L Q 9 θ z u hT.toE le_rfl huC huO hu1

end CFSG.OddStandard.AltStdSmall4
