module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.OddOmega
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.OddOrder8
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClShapes
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open KForm

theorem oddA6ModLeaf_of_inputs
    (hO : LieOrderFormulasInput) (hGLS : GLS3OddLieAutComponentsInput) : OddA6ModLeaf := by
  intro S _ _ hodd σ hσ D hDn hDiso hperf h26 h8
  have hA : A6Hyp σ D := ⟨hDn, hDiso, hperf⟩
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  obtain ⟨hp3, hshape, -⟩ := oddA6Shape_of_inputs hO hGLS t S n p f hp hp2 hadm hm σ hσ D hA
  subst hp3
  rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    obtain ⟨x, hx⟩ := order8Free_psl_two hadm hm hσ D hA
    exact absurd hx (h8 x)
  ·
    obtain ⟨x, hx⟩ := order8Free_psl_three hO hadm hm hσ D hA
    exact absurd hx (h8 x)
  ·
    rcases order8Or2Pow6_psl_four hO hadm hm hσ D hA with ⟨x, hx⟩ | h
    · exact absurd hx (h8 x)
    · exact absurd h h26
  ·
    obtain ⟨x, hx⟩ := order8Free_psu_three hO hadm hm hσ D hA
    exact absurd hx (h8 x)
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm))))
  ·
    exact Or.inr (Or.inl (Mod.lieModel_PSU_four_two_of_PSp_two_three hm))
  ·
    rcases order8Or2Pow6_psp_nine hadm hm hσ D hA with ⟨x, hx⟩ | h
    · exact absurd hx (h8 x)
    · exact absurd h h26
  ·
    exact absurd (pomegaOdd_two_pow_six hO hadm hm hσ hA) h26
  ·
    exact absurd (pomegaMinus_two_pow_six hO hadm hm hσ hA) h26

theorem oddA6ModLeaf_holds :
    OddA6ModLeaf :=
  oddA6ModLeaf_of_inputs CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.SeitzReduction.gls3OddLieAutComponentsInput

end CFSG.EvenSporadicStandard.M24Std
