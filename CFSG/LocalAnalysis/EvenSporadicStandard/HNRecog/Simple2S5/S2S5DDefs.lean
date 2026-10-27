module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5DData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def gElt (j : Nat) : Equiv.Perm (Fin 1408) := elemW (gWords.getD j [])

@[expose] noncomputable def wGroup : Subgroup (Equiv.Perm (Fin 1408)) :=
  Subgroup.closure ({yOne 0, yTwo 0, gElt jStar} : Set (Equiv.Perm (Fin 1408)))

structure DFacts : Prop where
  cover : ∀ h ∈ pPrime, h * (elemA * elemZ) * h⁻¹ = uElt 0 →
    (h * uElt 0 * h⁻¹ = elemA * elemZ ∨ h * uElt 0 * h⁻¹ = elemA * elemZ * uElt 0) →
      ∃ j < 16, (gElt j)⁻¹ * h ∈ yK 0
  jStar_lt : jStar < 16
  killed : ∀ j < 16, j ≠ jStar →
    elemA ∈ Subgroup.closure ({yOne 0, yTwo 0, gElt j} : Set (Equiv.Perm (Fin 1408)))
  fix : ∃ p : Fin 1408, yOne 0 p = p ∧ yTwo 0 p = p ∧ gElt jStar p = p
  sylow7 : ∃ Q ≤ wGroup, Nat.card ↥Q = 7
  sylow9 : ∃ Q ≤ wGroup, Nat.card ↥Q = 9
  sylow125 : ∃ Q ≤ wGroup, Nat.card ↥Q = 125

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
