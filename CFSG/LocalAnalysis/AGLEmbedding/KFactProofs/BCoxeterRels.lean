module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoxeter
public import CFSG.Sporadic.Bridge.BSurjInputs
import all CFSG.Sporadic.Bridge.Common
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.BabyMonster
import all TauCeti.GroupTheory.Presentation.Coxeter
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator
public import CFSG.Sporadic.Bridge.BData
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.AGLEmbedding.BCox

open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.B

@[expose] def cm (i j : Fin 11) : ℕ := if i = j then 1 else if adj i j then 3 else 2

theorem cox_mem : ∀ i j : Fin 11, i ≤ j →
    (List.replicate (cm i j) [(i.val, true), (j.val, true)]).flatten ∈ pres.relatorLetters := by
  decide +kernel

theorem cm_two : ∀ i j : Fin 11, i < j → adj i j = false → cm i j = 2 := by decide

theorem cm_three : ∀ i j : Fin 11, i < j → adj i j = true → cm i j = 3 := by decide

theorem presGen_eq_of (i : Fin pres.generatorCount) :
    presGen pres i.val = PresentedGroup.of i := by
  rw [presGen, dite_eq_left_of_eq_true (eq_true i.isLt)]

end CFSG.AGLEmbedding.BCox
