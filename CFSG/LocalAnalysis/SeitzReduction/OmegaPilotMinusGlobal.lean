module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverNodes

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore commutator_centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.Timmesfeld (edgeD)

theorem subgroupOf_iSup_of_le_minus {M : Type*} [Group M] {ι' : Sort*} {A : ι' → Subgroup M}
    {B : Subgroup M} (hA : ∀ j, A j ≤ B) :
    (⨆ j, A j).subgroupOf B = ⨆ j, (A j).subgroupOf B := by
  apply Subgroup.map_injective B.subtype_injective
  rw [subgroupOf_map_subtype, Subgroup.map_iSup, inf_eq_left.2 (iSup_le hA)]
  exact iSup_congr fun j => by rw [subgroupOf_map_subtype, inf_eq_left.2 (hA j)]

theorem commutator_iSup_of_perfect {M : Type*} [Group M] {ι' : Sort*} {A : ι' → Subgroup M}
    (hA : ∀ j, ⁅A j, A j⁆ = A j) : ⁅⨆ j, A j, ⨆ j, A j⁆ = ⨆ j, A j :=
  le_antisymm (Subgroup.commutator_le_self _) (iSup_le fun j =>
    (hA j).symm.le.trans (Subgroup.commutator_mono (le_iSup A j) (le_iSup A j)))

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}

omit [Finite F] [CharP F 2] in
theorem minusNode_succ_le (hC : ∀ k, MinusFieldCover e ι k) (j : Fin (r + 1)) :
    minusNode (hC 0) j.succ ≤ minusNeighbourCore e (0 : Fin (r + 1)) := by
  rcases (show j.val + 2 ≤ r ∨ r ≤ j.val + 1 by omega) with h | h
  · rw [minusNode_of_le _ (show j.succ.val + 1 ≤ r by rw [Fin.val_succ]; omega)]
    refine minusLevelCore_le_minusNeighbourCore e ?_
    rw [mem_consecutiveBlock, Fin.val_zero, Fin.val_succ]
    omega
  · rcases (show j.succ.val = r ∨ j.succ.val = r + 1 by rw [Fin.val_succ]; omega) with h' | h'
    · rw [minusNode_of_eq _ h']
      exact (hC 0).lift_le _
    · rw [minusNode_of_eq_succ _ h']
      exact (hC 0).lift_le _

omit [CharP F 2] in
theorem map_minusNode_succ (hr : 2 ≤ r) (hC : ∀ k, MinusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) (j : Fin (r + 1)) :
    (((minusNode (hC 0) j.succ).subgroupOf (minusNeighbourCore e (0 : Fin (r + 1)))).map
        (hC 0).π).map (StatedOmega (StatedQuadPlus (r + 1) F)).subtype =
      siegelNode F (r + 1) j := by
  rcases (show j.val + 2 ≤ r ∨ j.val + 1 = r ∨ j.val = r by omega) with h | h | h
  · have hj : j.succ.val + 1 ≤ r := by rw [Fin.val_succ]; omega
    have h0 : (0 : Fin (r + 1)) ∉ consecutiveBlock (r + 1) j.succ.val 2 := by
      rw [mem_consecutiveBlock, Fin.val_zero, Fin.val_succ]
      omega
    rw [minusNode_of_le _ hj, (hC 0).map_levelCore hK hF h0
      (card_consecutiveBlock_two (by rw [Fin.val_succ]; omega)).ge,
      castSuccPlanes_preimagePlanes_zero (by rw [Fin.val_succ]; omega) hj, siegelNode]
    have hflip : plusNodeFlip (r + 1) j = ∅ := by
      ext x
      rw [mem_plusNodeFlip]
      simp only [Finset.notMem_empty, iff_false]
      omega
    have hset : plusNodeSet (r + 1) j = consecutiveBlock (r + 1) (j.succ.val - 1) 2 := by
      ext x
      rw [mem_plusNodeSet, mem_consecutiveBlock, Fin.val_succ]
      have := x.isLt
      omega
    rw [hflip, flipGL_empty, map_conj_one_eq, hset]
  · have hj : j.succ.val = r := by rw [Fin.val_succ]; omega
    rw [minusNode_of_eq _ hj, (hC 0).map_lift (forkBlock_le_statedOmega hF (by omega) ∅)
      (commutator_forkBlock hF (by omega) ∅), forkBlock, siegelNode]
    have hflip : plusNodeFlip (r + 1) j = ∅ := by
      ext x
      rw [mem_plusNodeFlip]
      simp only [Finset.notMem_empty, iff_false]
      omega
    have hset : plusNodeSet (r + 1) j = consecutiveBlock (r + 1) (r - 1) 2 := by
      ext x
      rw [mem_plusNodeSet, mem_consecutiveBlock]
      have := x.isLt
      omega
    rw [hflip, hset]
  · have hj : j.succ.val = r + 1 := by rw [Fin.val_succ]; omega
    rw [minusNode_of_eq_succ _ hj, (hC 0).map_lift (forkBlock_le_statedOmega hF (by omega) _)
      (commutator_forkBlock hF (by omega) _), forkBlock, siegelNode]
    have hflip : plusNodeFlip (r + 1) j = {Fin.last r} := by
      ext x
      rw [mem_plusNodeFlip, Finset.mem_singleton, Fin.ext_iff, Fin.val_last]
      omega
    have hset : plusNodeSet (r + 1) j = consecutiveBlock (r + 1) (r - 1) 2 := by
      ext x
      rw [mem_plusNodeSet, mem_consecutiveBlock]
      have := x.isLt
      omega
    rw [hflip, hset]

theorem minusNeighbourCore_zero_le_iSup (hr : 3 ≤ r) (hC : ∀ k, MinusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) {f' : ℕ} (hF' : Nat.card F = 2 ^ f') (hF : 4 ≤ Nat.card F) :
    minusNeighbourCore e (0 : Fin (r + 1)) ≤ ⨆ j : Fin (r + 1), minusNode (hC 0) j.succ := by
  set E := minusNeighbourCore e (0 : Fin (r + 1)) with hE
  set X := ⨆ j : Fin (r + 1), minusNode (hC 0) j.succ with hX
  have hXE : ∀ j : Fin (r + 1), minusNode (hC 0) j.succ ≤ E := minusNode_succ_le hC
  have hXp : ⁅X, X⁆ = X := commutator_iSup_of_perfect fun j => commutator_minusNode _ _
  set π' := (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp (hC 0).π with hπ'
  have himg : (X.subgroupOf E).map π' = StatedOmega (StatedQuadPlus (r + 1) F) := by
    rw [hX, subgroupOf_iSup_of_le_minus hXE, Subgroup.map_iSup]
    have h1 : ∀ j : Fin (r + 1), ((minusNode (hC 0) j.succ).subgroupOf E).map π' =
        siegelNode F (r + 1) j := fun j => by
      rw [hπ', ← Subgroup.map_map]
      exact map_minusNode_succ (by omega) hC hK hF j
    simp only [h1]
    exact iSup_siegelNode_eq_statedOmega (by omega) hF' hF
  have hrange : (⊤ : Subgroup E).map π' = StatedOmega (StatedQuadPlus (r + 1) F) := by
    rw [← MonoidHom.range_eq_map, hπ', MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (hC 0).surjective, ← MonoidHom.range_eq_map, range_subtype]
  have hA : ⁅(⊤ : Subgroup E), (⊤ : Subgroup E)⁆ = (⊤ : Subgroup E) := by
    have h := commutator_subgroupOf_eq_of_le_perfect (le_refl E)
      (commutator_centralizerPerfectCore (modelToG e (minusPairTorus hn b c (0 : Fin (r + 1)))))
    rwa [Subgroup.subgroupOf_self] at h
  have hB := commutator_subgroupOf_eq_of_le_perfect (iSup_le hXE) hXp
  have hle := le_of_map_le_of_perfect (hC 0).ker_comp_subtype_le hA hB (by rw [hrange, himg])
  intro x hx
  exact hle (Subgroup.mem_top (⟨x, hx⟩ : E))

omit [CharP F 2] in
theorem minusNode_le_minusPieceCore_of_le (hr : 1 ≤ r) (hC : ∀ k, MinusFieldCover e ι k)
    (hF : 4 ≤ Nat.card F) {j : Fin (r + 2)} (hj : r ≤ j.val) :
    minusNode (hC 0) j ≤ minusPieceCore e {Fin.last r} := by
  rcases (show j.val = r ∨ j.val = r + 1 by omega) with h | h
  · rw [minusNode_of_eq _ h]
    exact lift_forkBlock_le_minusPieceCore (hC 0) hF hr (Finset.empty_subset _)
  · rw [minusNode_of_eq_succ _ h]
    exact lift_forkBlock_le_minusPieceCore (hC 0) hF hr le_rfl

end Global

end CFSG.SeitzReduction.OmegaPilot
