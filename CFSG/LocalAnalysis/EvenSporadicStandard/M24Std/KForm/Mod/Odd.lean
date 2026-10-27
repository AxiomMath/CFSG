module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.OddLeaf
public import CFSG.Adapters.ClassicalCatalogReverse

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem z2s6_mod_odd_arm (hOB : OddLieA6TwoComponent) (hL : OddA6ModLeaf) {S : Type}
    [Group S] [Finite S] (hodd : OddLieType S) {σ : MulAut S}
    {J : Subgroup ↥(fixedSubgroup σ)} (hdata : Z2S6ModData S σ J) : Z2S6Socle S := by
  obtain ⟨e⟩ := hOB S hodd σ hdata.order_two J hdata.isPComponent hdata.iso
  exact hL S hodd σ hdata.order_two J hdata.normal ⟨e⟩ hdata.perfect_le
    hdata.not_two_pow_six hdata.no_eight

theorem lieModel_PSU_four_two_of_PSp_two_three {G : Type} [Group G]
    (h : LieModel G .PSp 2 3 1) : LieModel G .PSU 4 2 1 :=
  Or.inl ⟨by decide,
    CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three
      (h.statedClassicalModel (by decide))⟩

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
