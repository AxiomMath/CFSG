module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Held
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.H13.FiveMenu

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial
open scoped MatrixGroups

theorem transvection15_eq_cornerTransvection :
    Quasithin.H13.transvection15 = DW.cornerTransvection (N := 5) (by norm_num) :=
  rfl

theorem heldTypeRecognition_of_asc94 (h : Quasithin.H13.Asc94_M24He_L52Type) :
    HeldTypeRecognition := by
  intro G _ _ _ z hz hC hwc
  have hC' : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({Quasithin.H13.transvection15} : Set (SL(5, ZMod 2)))) := by
    rw [transvection15_eq_cornerTransvection]
    exact hC
  rcases (h G z inferInstance hz hC' hwc).1 with hL | hM | hH
  · obtain ⟨e⟩ := Quasithin.H13.nonempty_mulEquiv_sl_two_of_lieModel hL
    exact Or.inl ⟨e.trans (DW.slEquivPSL 5)⟩
  · exact Or.inr (Or.inl hM)
  · exact Or.inr (Or.inr hH)

end CFSG.ComponentClassification.AS81
