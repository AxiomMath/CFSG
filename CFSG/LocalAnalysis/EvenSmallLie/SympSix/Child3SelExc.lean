module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelExcCore
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenAssembly
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddAssembly

public section

namespace CFSG.EvenSmallLie.Child3.SelExc

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Exclusion

variable {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal]
  (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
  (hJD : J ≤ D) (hJa : J ≤ centralizer ({a} : Set Y))
  (hC : zpowers a ⊔ J = centralizer ({a} : Set Y))
  (hJ : Nonempty (J ≃* GL (Fin 3) (ZMod 2)))
include hCD ha hJD hJa hC hJ

theorem false_of_chevalleyExceptionalModel {t : StatedLieTag} {p f : ℕ}
    (hD : ChevalleyExceptionalModel D t p f) : False := by
  by_cases hp2 : p = 2
  · subst hp2
    exact false_of_noSmallComponent hCD ha hJD hJa hC hJ
        (ComponentClassification.ExcSelector.noSmallComponent_of_model_even hD)
  · exact false_of_noSmallComponent hCD ha hJD hJa hC hJ
      (ComponentClassification.ExcSelector.noSmallComponent_of_model_odd hp2 hD)

theorem false_of_lieModel_of_mem_chevalleyExceptionalTags {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (hD : LieModel D t n p f) : False := by
  rcases hD with ⟨ht', -⟩ | ⟨-, -, h⟩ | ⟨-, ht', -⟩ | ⟨-, rfl, -⟩
  · revert ht ht'
    cases t <;> decide
  · exact false_of_chevalleyExceptionalModel hCD ha hJD hJa hC hJ h
  · revert ht ht'
    cases t <;> decide
  · exact absurd ht (by decide)

end Exclusion

end CFSG.EvenSmallLie.Child3.SelExc
