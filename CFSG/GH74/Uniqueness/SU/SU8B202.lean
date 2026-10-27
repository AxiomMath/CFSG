module

public import CFSG.GH74.Uniqueness.SU.SU8BTr
public import CFSG.GH74.Uniqueness.SU.SU8BHyp
public import CFSG.GH74.Uniqueness.SU.SU8Final
public import CFSG.GH74.Uniqueness.SU.SU8BK3

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.Setup

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

theorem Hyp20A.center_eq_bot (hKI5 : K.KI5) (hyp : Hyp20A z S L A) :
    center ↥(hbarImage (Hz z) L) = ⊥ := by
  rcases hyp.L_bender with h | ⟨hSz⟩
  · obtain ⟨n, i, e, hBT⟩ := isBenderGroup_iff_exists_benderType.mp h
    exact hBT.center_eq_bot
  · by_contra hne
    have := hyp.normal_subgroupOf
    have hqs : IsQuasisimple ↥(hbarImage (Hz z) L) := by
      obtain ⟨Kc, hKc, -, hmap, -⟩ := hyp.L_comp.2
      have h1 : hbarImage (Hz z) L = Kc := hmap
      rw [h1]
      exact hKc.1
    have hzH : z ∈ Hz z :=
      Subgroup.mem_centralizer_iff.mpr (fun y hy => by rw [Set.mem_singleton_iff.mp hy])
    have hzA : (⟨z, hzH⟩ : ↥(Hz z)) ∈ BLift.ACx (pPrimeCore 2 ↥(Hz z)) (L.subgroupOf (Hz z))
        (A.subgroupOf (Hz z)) := by
      rw [ACx_eq]
      exact Subgroup.mem_subgroupOf.mpr hyp.z_mem
    have hz1 : (⟨z, hzH⟩ : ↥(Hz z)) ≠ 1 := fun h => hyp.z_ne_one (congrArg Subtype.val h)
    have cbX := BK.caseB_of_K hyp.preHyp (pPrimeCore_hbar (Hz z)) hqs hne hSz hKI5 hzA hz1
    rw [ACx_eq] at cbX
    refine hyp.false_of_caseB (CaseB.of_subgroupOf hyp.L_le hyp.A_le_H
      (inf_le_left.trans hyp.A_le_H) hzH (fun g hg => ?_) cbX)
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact hg.symm)

theorem lemma202 (hKI5 : K.KI5) : Lemma202Stmt := by
  intro G _ _ z S L A hyp
  exact hyp.center_eq_bot hKI5

theorem prop201
    (hKI5 : K.KI5) : Prop201Stmt := prop201_of_202 (lemma202 hKI5)

end CFSG.GH74.Uniqueness.SU.SU8
