module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.Blueprint

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X]

theorem LieModel.card_outer_psu {n p f : ℕ} (h : LieModel X .PSU n p f) (hn : 3 ≤ n)
    (hq : ¬ (n = 3 ∧ p ^ f = 2)) :
    Nat.card (Outer X) = 2 * f * Nat.gcd n (p ^ f + 1) := by
  obtain ⟨⟨hp, hf, -, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by omega)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hout :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU hn hq
  have e' : X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := n) (by omega)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact hout.2.2.2.2.1

end CFSG.Blueprint
