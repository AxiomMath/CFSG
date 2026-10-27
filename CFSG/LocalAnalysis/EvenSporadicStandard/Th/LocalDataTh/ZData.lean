module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ABasis
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaData

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th.Max3
open scoped Matrix

@[expose] def psi0 : Fin 3 → ZMod 2 := ![1, 1, 0]

@[expose] def vZ : Vec := codeVec 8 10

@[expose] def rhoGc : List (List ℕ) :=
  [wordCols wG1, idCols 8, wordCols wG3, wordCols wG4]

@[expose] def rhoG (i : Fin 4) : Mat8 := matOfCols 8 (rhoGc.getD i (idCols 8))

@[expose] def HZFacts : Prop :=
  (∀ a ∈ Pc, (∀ (i : Fin 8) (j : Fin 3),
      CFSG.Certificates.ExtraspecialNF.bil c ((matOfCols 8 a + 1) *ᵥ (Pi.single i 1 : Vec))
        (uVec j) = 0) →
      ∀ j : Fin 3, matOfCols 8 a *ᵥ uVec j = uVec j) ∧
  (∀ ψ : Fin 3 → ZMod 2, (∀ a ∈ Pc, ∀ P : Matrix (Fin 3) (Fin 3) (ZMod 2),
      (∀ j, matOfCols 8 a *ᵥ uVec j = ∑ i, P i j • uVec i) → ∀ j, ∑ i, P i j * ψ i = ψ j) →
      ψ = 0 ∨ ψ = psi0) ∧
  (∀ j : Fin 3, CFSG.Certificates.ExtraspecialNF.bil c vZ (uVec j) = psi0 j) ∧
  (∃ a ∈ Pc, ∃ i : Fin 4, (rhoG i + 1) *ᵥ ((matOfCols 8 a + 1) *ᵥ vZ) ≠ 0)

set_option synthInstance.maxSize 1000 in
instance : Decidable HZFacts := by unfold HZFacts; infer_instance

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
