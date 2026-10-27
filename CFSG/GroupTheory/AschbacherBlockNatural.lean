module

public import CFSG.GroupTheory.AschbacherBlock
import CFSG.GroupTheory.AschbacherBlockMap
import CFSG.GroupTheory.NaturalModuleChief

public section

namespace CFSG.GroupTheory

open CFSG CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

theorem isAschbacherBlockGomi_top_of_isNaturalModule {B : Type} [Group B]
    (hres : oResidualTwo B = ⊤)
    (hq : IsQuasisimple (B ⧸ pCore 2 B) ∨
      ((Nat.card (B ⧸ pCore 2 B)).Prime ∧ Odd (Nat.card (B ⧸ pCore 2 B))))
    (hU : ⁅pCore 2 B, (⊤ : Subgroup B)⁆ ≤ omegaOneCenterIn (pCore 2 B))
    (h : (∃ n, 2 ≤ n ∧ IsNaturalSLTwoModule B n) ∨ ∃ n, 1 ≤ n ∧ IsNaturalAltModule B n) :
    IsAschbacherBlockGomi (⊤ : Subgroup B) :=
  isAschbacherBlockGomi_of_mulEquiv (Y' := B) (B' := ⊤) Subgroup.topEquiv.symm hres hq
    (exists_chief_of_isNaturalModule h) Subgroup.IsSubnormal.top hU

end CFSG.GroupTheory
