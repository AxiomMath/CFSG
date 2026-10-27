module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Transfer
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.LeviBasic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLChev
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.ModelSp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbFamF4

public section

namespace CFSG.GroupTheory.GomiLeviExc.F4

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.Adjoint CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.SeitzReduction.F4Pilot CFSG.RankThree.Chevalley

private theorem eq_zero_of_not_mem_one_two_three {k : Fin (Tag.rank .F4)}
    (hk : k ∉ ({1, 2, 3} : Set (Fin (Tag.rank .F4)))) : k = 0 := by
  revert k
  decide

private theorem eq_three_of_not_mem_zero_one_two {k : Fin (Tag.rank .F4)}
    (hk : k ∉ ({0, 1, 2} : Set (Fin (Tag.rank .F4)))) : k = 3 := by
  revert k
  decide

section Symplectic

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem leviM_one_two_eq_B2Levi : leviM (f4Datum K) {1, 2} = B2Levi K := by
  have h : leviM (f4Datum K) ((({1, 2} : Finset (Fin (Tag.rank .F4)))) : Set (Fin (Tag.rank .F4))) =
      B2Levi K :=
    levi_one_two_eq_B2Levi
  rwa [Finset.coe_insert, Finset.coe_singleton] at h

theorem gomiLeviFactor_leviM_one_two : GomiLeviFactor ↥(leviM (f4Datum K) {1, 2}) :=
  GomiLeviFactor.of_mulEquiv
    ((b2LeviEquiv K).trans (MulEquiv.subgroupCongr leviM_one_two_eq_B2Levi.symm))
    (gomiLeviFactor_statedSp K le_rfl)

omit [Finite K] [CharP K 2] in
theorem leviM_one_two_three_eq_C3Levi : leviM (f4Datum K) {1, 2, 3} = C3Levi K := by
  refine le_antisymm ?_ ?_
  · have h : leviM (f4Datum K)
        ((({1, 2, 3} : Finset (Fin (Tag.rank .F4)))) : Set (Fin (Tag.rank .F4))) ≤
        C3Levi K := by
      rw [leviM_coe_finset]
      exact levi_le_C3Levi (K := K) (J := {1, 2, 3}) (by decide)
    rwa [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton] at h
  · rw [C3Levi_eq_iSup_rootGroup]
    refine iSup₂_le fun γ hγ => ?_
    refine rootGroup_le_leviM (hct := f4_isCTGroupDatum K) (mem_adjDatum_roots.2 hγ.1) ?_
    intro k hk
    rw [eq_zero_of_not_mem_one_two_three hk]
    simpa using hγ.2

theorem gomiLeviFactor_leviM_one_two_three : GomiLeviFactor ↥(leviM (f4Datum K) {1, 2, 3}) :=
  GomiLeviFactor.of_mulEquiv
    ((c3LeviEquiv K).trans (MulEquiv.subgroupCongr leviM_one_two_three_eq_C3Levi.symm))
    (gomiLeviFactor_statedSp K (by norm_num))

end Symplectic

section B3Generation


variable {K : Type} [Field K]

private theorem B3Levi_eq_iSup_rootGroup :
    B3Levi K = ⨆ γ ∈ b3LeviRoots, (f4Datum K).rootGroup γ := by
  have hmap : (B3Levi K).map (adjointGroup .F4 K).subtype = rootSpan .F4 K b3LeviRoots := by
    rw [B3Levi, subgroupOf_map_subtype, inf_of_le_left]
    exact iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  apply map_injective (adjointGroup .F4 K).subtype_injective
  rw [hmap, rootSpan, Subgroup.map_iSup]
  refine iSup_congr fun γ => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hγ => (map_subtype_rootGroup (K := K) hγ.1).symm

end B3Generation

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem gomiLeviFactor_leviM_a2 (κ : F4A2Kind) :
    GomiLeviFactor ↥(leviM (f4Datum K) {κ.i, κ.j}) := by
  have : Finite ↥(adjointGroup .F4 K) := CFSG.LieType.Chevalley.generated_group_finite .F4 K
  obtain ⟨l, hl, hrange⟩ := CFSG.AGLEmbeddingD2.Tits.GN516.Fam.exists_sl3_range (K := K) κ
  have hsl := CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_sl (k := 3)
    (F := K) (Or.inl le_rfl)
  exact gomiLeviFactor_of_injective hsl.1
    (Nat.not_even_iff_odd.mp fun h =>
      CFSG.ClassicalInvolution.ModelFacts.LinearAut.not_dvd_card_center_specialLinearGroup
        (p := 2) (even_iff_two_dvd.mp h))
    (isChevTwo_of_classicalTwoOrG2 hsl.2) l hl
    (hrange.trans (leviM_pair (f4Datum K) κ.i κ.j).symm)

theorem gomiLeviFactor_leviM_zero_one : GomiLeviFactor ↥(leviM (f4Datum K) {0, 1}) :=
  gomiLeviFactor_leviM_a2 .long

theorem gomiLeviFactor_leviM_two_three : GomiLeviFactor ↥(leviM (f4Datum K) {2, 3}) :=
  gomiLeviFactor_leviM_a2 .short

omit
  [Finite K] [CharP K 2] in
theorem leviM_zero_one_two_eq_B3Levi : leviM (f4Datum K) {0, 1, 2} = B3Levi K := by
  refine le_antisymm ?_ ?_
  · have h : leviM (f4Datum K)
        ((({0, 1, 2} : Finset (Fin (Tag.rank .F4)))) : Set (Fin (Tag.rank .F4))) ≤
        B3Levi K := by
      rw [leviM_coe_finset]
      exact levi_le_B3Levi (K := K) (J := {0, 1, 2}) (by decide)
    rwa [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton] at h
  · rw [B3Levi_eq_iSup_rootGroup]
    refine iSup₂_le fun γ hγ => ?_
    refine rootGroup_le_leviM (hct := f4_isCTGroupDatum K) (mem_adjDatum_roots.2 hγ.1) ?_
    intro k hk
    rw [eq_three_of_not_mem_zero_one_two hk]
    exact hγ.2

theorem gomiLeviFactor_leviM_zero_one_two : GomiLeviFactor ↥(leviM (f4Datum K) {0, 1, 2}) :=
  GomiLeviFactor.of_mulEquiv
    ((b3LeviEquiv (K := K)).trans (MulEquiv.subgroupCongr leviM_zero_one_two_eq_B3Levi.symm))
    (gomiLeviFactor_statedSp K (by norm_num))

end Frame

end CFSG.GroupTheory.GomiLeviExc.F4
