module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBFixed

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)

theorem bTwo_psu {X : Type} [Group X] [Finite X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU n p f)
    (hm : CFSG.Blueprint.LieModel X .PSU n p f) (hZ : Subgroup.center X = ⊥) {z : X}
    (hz : orderOf z = 2) : BTwo X z := by
  have hn : 3 ≤ n := hadm.2.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (X ≃* StatedProj (StatedSU n (p ^ f) K)) := by
    rcases hm with ⟨-, h⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
    · obtain ⟨-, K, _, _, hK, e⟩ := h
      exact ⟨K, inferInstance, inferInstance, hK, e⟩
    all_goals omega
  have hU : UnitaryFieldData p f K := ⟨hp, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
  let e' : X ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  have hα : orderOf (MulAut.congr e' (MulAut.conj z)) = 2 :=
    (MulEquiv.orderOf_eq (MulAut.congr e') _).trans (orderOf_conj_eq_two hZ hz)
  intro S hS
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv 2
    (CatalogueRelativeB.fixedSubgroupEquivalence e' (MulAut.conj z))
    (fun L hL => CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components hU hp2 hn _ hα 2
      Nat.prime_two L hL) S hS

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
