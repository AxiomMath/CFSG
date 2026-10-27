module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcToral
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.HardMathSupport.C14Idx

private lemma rootChar_mulSingle_apply {τ : Tag} {L : Type} [Field L]
    (i : Fin τ.rank) (c : Lˣ) (α : Fin τ.rank → ℤ) :
    rootChar (Pi.mulSingle i c) α = c ^ α i := by
  classical
  rw [rootChar, Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, one_zpow]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem familyGroup_le_adjointGroup {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) :
    familyGroup (K := L) a ≤ adjointGroup τ L := by
  unfold familyGroup
  exact sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
    (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L (familyKernel a))

private theorem rootSubgroup_le_commutator_torus_sup_rootSpan {τ : Tag} {L : Type} [Field L]
    {ι : Type}
    [IsAlgClosed L]
    (a : ι → Fin τ.rank → Lˣ) {α : Fin τ.rank → ℤ} (hα : α ∈ familyKernel a) :
    rootSubgroup τ L α ≤
      ⁅torusGroup τ L ⊔ rootSpan τ L (familyKernel a),
        torusGroup τ L ⊔ rootSpan τ L (familyKernel a)⁆ := by
  have hαroot : IsRoot τ α := hα.1
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := Function.ne_iff.1 hαroot.ne_zero
  obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.ModelFacts.Levi.exists_unit_pow_ne_one
    (k := L) (α i).natAbs
  have hc' : c ^ α i ≠ 1 := by
    intro h
    refine hc (α i).natAbs (Nat.succ_le_of_lt (Int.natAbs_pos.2 hi)) le_rfl ?_
    have h' : c ^ |α i| = 1 := (zpow_abs_eq_one c (α i)).2 h
    rwa [Int.abs_eq_natAbs, zpow_natCast] at h'
  have htchar : rootChar (Pi.mulSingle i c) α ≠ 1 := by
    simpa [rootChar_mulSingle_apply] using hc'
  have htT : rootDiagUnit τ (Pi.mulSingle i c) ∈ torusGroup τ L :=
    rootDiagUnit_mem_torusGroup (Pi.mulSingle i c)
  have hUR : rootSubgroup τ L α ≤ torusGroup τ L ⊔ rootSpan τ L (familyKernel a) :=
    (le_iSup₂_of_le (f := fun β (_ : β ∈ familyKernel a) => rootSubgroup τ L β) α hα
      le_rfl).trans le_sup_right
  exact CFSG.SeitzReduction.F4Pilot.rootSubgroup_le_commutator_of_rootChar_ne_one
    hαroot htchar (Subgroup.mem_sup_left htT) hUR

theorem map_famS_subtype_eq_rootSpan {τ : Tag} {L : Type} [Field L] {ι : Type}
    [IsAlgClosed L]
    (a : ι → Fin τ.rank → Lˣ) :
    (famS a).map (adjointGroup τ L).subtype = rootSpan τ L (familyKernel a) := by
  have hfam : (famM a).map (adjointGroup τ L).subtype = familyGroup a := by
    unfold famM
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (familyGroup_le_adjointGroup a)]
  unfold famS
  rw [Subgroup.map_commutator, hfam]
  refine le_antisymm ?_ ?_
  · unfold familyGroup
    exact CFSG.StandardType.LayerExc.commutator_torus_sup_rootSpan_le fun α hα => hα.1
  · unfold familyGroup
    exact iSup₂_le fun α hα => rootSubgroup_le_commutator_torus_sup_rootSpan a hα

end CFSG.HardMathSupport.C14Idx
