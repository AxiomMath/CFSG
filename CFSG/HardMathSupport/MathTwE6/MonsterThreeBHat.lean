module

public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBAut
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeB

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open CFSG.Open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_mulAut_dvd_of_perfect {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤) :
    Nat.card (MulAut X) ∣ Nat.card (MulAut (X ⧸ Subgroup.center X)) := by
  haveI := finite_mulAut (X ⧸ Subgroup.center X)
  exact Subgroup.card_dvd_of_injective _
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hX)

theorem centralizer_zpowers_tbw :
    Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) =
      Subgroup.centralizer ({tbw} : Set Gmat) := by
  rw [Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_closure {tbw}

theorem map_conj_centralizer (c s : Gmat) :
    (Subgroup.centralizer ({s} : Set Gmat)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * s * c⁻¹} : Set Gmat) := by
  ext z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc z * (c * s * c⁻¹) = c * (c⁻¹ * z * c * s) * c⁻¹ := by group
      _ = c * (s * (c⁻¹ * z * c)) * c⁻¹ := by rw [h]
      _ = c * s * c⁻¹ * z := by group
  · intro h
    calc c⁻¹ * z * c * s = c⁻¹ * (z * (c * s * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * s * c⁻¹ * z) * c := by rw [h]
      _ = s * (c⁻¹ * z * c) := by group

end CFSG.HardMathSupport.MathTwE6.M3BIrr
