module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSp

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.AGLEmbedding.ParabAutIrr CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped commutatorElement

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isMulCommutative_borel_quotient_sp (hm : 3 ≤ m)
    (B : Subgroup (StatedSp m F))
    (hB : B = Subgroup.normalizer (unipotent m F : Set (StatedSp m F))) :
    IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B) := by
  rw [hB, normalizer_unipotent]
  set B' : Subgroup (StatedSp m F) := borelSubgroup m F with hB'
  set U : Subgroup (StatedSp m F) := unipotent m F with hU
  have hUle : U ≤ B' := unipotent_le_borelSubgroup
  haveI hUn : (U.subgroupOf B').Normal := unipotent_subgroupOf_borelSubgroup_normal
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 m
  have hP' : (P : Subgroup (StatedSp m F)) = U := hP.trans hU.symm
  have hU2 : IsPGroup 2 U := hP' ▸ P.isPGroup'
  have hU2' : IsPGroup 2 (U.subgroupOf B') :=
    hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUle).symm
  have hUcore : U.subgroupOf B' ≤ CFSG.pCore 2 ↥B' := le_sSup ⟨inferInstance, hU2'⟩
  have hcomm : _root_.commutator ↥B' ≤ U.subgroupOf B' := by
    change ⁅(⊤ : Subgroup ↥B'), ⊤⁆ ≤ U.subgroupOf B'
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [Subgroup.mem_subgroupOf]
    simpa [U, commutatorElement_def] using commutator_mem_unipotent g.2 h.2
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (hcomm.trans hUcore)

end CFSG.ClassicalGroups.Symplectic
