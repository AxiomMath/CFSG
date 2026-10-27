module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.Klein

open CFSG Subgroup Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

variable
  {K : Type} [Field K] [Finite K] {b c : K}

theorem isPerfect_spinGroup_quadMinus_three (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsPerfect (spinGroup (quadMinus 3 K b c)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have hE4 := four_le_card_shortField' (b := b) (c := c)
  have : Group.IsPerfect (SL(2, K)) :=
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr (by omega))
      (Or.inr (by omega))).1
  have : Group.IsPerfect (SL(2, ShortField b c)) :=
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (ShortField b c) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))).1
  have hsup := ClassicalInvolution.WeakCT.spinMinus6_blocks_sup_eq_top hirr h2
  have : Group.IsPerfect (minusLongBlock b c).range := Group.IsPerfect.range _
  have : Group.IsPerfect (shortBlock hirr 3 finOne).range := Group.IsPerfect.range _
  refine ⟨top_le_iff.mp ?_⟩
  rw [← hsup, _root_.commutator_def]
  exact sup_le (Subgroup.commutator_eq_self.symm.le.trans (Subgroup.commutator_mono le_top le_top))
    (Subgroup.commutator_eq_self.symm.le.trans (Subgroup.commutator_mono le_top le_top))

theorem range_spinAction_quadMinus_three_eq_commutator (hodd : Odd (Nat.card K))
    (h4 : 4 ≤ Nat.card K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (spinAction (quadMinus 3 K b c)).range =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  have := isPerfect_spinGroup_quadMinus_three hodd h4 hirr
  have hE := ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three hirr
  have hle : (spinAction (quadMinus 3 K b c)).range ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c) :=
    hE ▸ elementaryGroup_le_orthogonalGroup _
  have : Group.IsPerfect (spinAction (quadMinus 3 K b c)).range := Group.IsPerfect.range _
  refine le_antisymm ?_ ?_
  · calc (spinAction (quadMinus 3 K b c)).range =
          ⁅(spinAction (quadMinus 3 K b c)).range, (spinAction (quadMinus 3 K b c)).range⁆ :=
        Subgroup.commutator_eq_self.symm
      _ ≤ _ := Subgroup.commutator_mono hle hle
  · rw [hE]
    refine commutator_le_of_le_closure (fun g hg x hx => conj_mem_elementaryGroup hg hx)
      (elementaryGroup_le_orthogonalGroup _) ?_
      ((orthogonalGroup_le_closure_reflect h2 hQ).trans
        (Subgroup.closure_mono Set.subset_union_left)) ?_
    · rintro _ ⟨v, rfl⟩
      exact reflect_mem_orthogonalGroup _ v
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      exact commutatorElement_reflect_mem hQ (minusPair_orth (K := K) (b := b) (c := c)
        (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp)) u v

end CFSG.ComponentClassification.HarrisLit.T1.P54.Klein
