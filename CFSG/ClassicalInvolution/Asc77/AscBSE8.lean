module

public import CFSG.ClassicalInvolution.Asc77.AscBSE3
public import CFSG.ClassicalInvolution.Asc77.AscBSE7

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.BSC.BSD
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime]

theorem bootNoManyTwinsD4_of_five (h : BootNoD4FiveComp p f) : BootNoManyTwinsD4 p f := by
  intro G _ _ _ K z hS D i hi
  obtain ⟨hD4, hrank⟩ := hi
  by_contra hlt
  have hno := noFuzzyFrame hS
  let C := NDB.Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D
  have hD4' : C.D.tag i = .POmegaPlus := hD4
  have hrank' : C.D.rank i = 4 := hrank
  have hcard : 3 < C.D.card := by
    show 3 < D.card
    omega
  by_cases h4 : D.card = 4
  · exact false_of_d4_four (C := C) hno (b := i) hD4' hrank' h4
  by_cases h5 : D.card = 5
  · exact h G K z hS D i ⟨hD4, hrank⟩ h5
  · have h6 : 6 ≤ C.D.card := by
      show 6 ≤ D.card
      omega
    exact false_of_d4_many (C := C) hno (b := i) hD4' hrank' h6

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
