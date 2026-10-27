module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClData

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput GLS3OddLieAutComponentsInput)

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

@[expose] def GomiU42NoU43 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J D E : Subgroup X) (a : X), GomiU42Data X J D E a →
    LieModel ↥D .PSU 4 3 1 → False

theorem GomiU42Data.false_of_classical_of_families (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hPSL : OddU42Free .PSL) (hPSU : OddU42ShapePSU)
    (hPSp : OddU42Free .PSp) (hPOO : OddU42Free .POmegaOdd) (hPOP : OddU42Free .POmegaPlus)
    (hPOM : OddU42Free .POmegaMinus) (hU43 : GomiU42NoU43) (h : GomiU42Data X J D E a)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ∈ classicalTags)
    (hD : StatedClassicalModel ↥D t n p f) : False := by
  haveI := h.normal
  have hm : LieModel ↥D t n p f := Or.inl ⟨ht, hD⟩
  have hadm : StatedLieAdmissible t n p f := hm.admissible
  have hp3 : p = 3 := h.p_eq_three hGLS hO hp hp2 hadm hm
  subst hp3
  have hσ := h.fixedRoot_conjNormal.1
  have hhyp := h.u42Hyp
  cases t
  · exact hPSL ↥D n f hadm hm _ _ hσ hhyp
  · obtain ⟨rfl, rfl⟩ := hPSU ↥D n f hadm hm _ _ hσ hhyp
    exact hU43 X J D E a h hm
  · exact hPSp ↥D n f hadm hm _ _ hσ hhyp
  · exact hPOO ↥D n f hadm hm _ _ hσ hhyp
  · exact hPOP ↥D n f hadm hm _ _ hσ hhyp
  · exact hPOM ↥D n f hadm hm _ _ hσ hhyp
  all_goals exact absurd ht (by decide)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
