module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinMain
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Leaves
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open scoped MatrixGroups

theorem ivk95l_empty_psl {m : ℕ} (hm : m = 4 ∨ m = 5) {p f : ℕ} (hodd : Odd (p ^ f)) :
    Ivk95Empty (fun X _ => LieModel X .PSL m p f) := by
  intro J _ _ hJ z hz q hq hq5 hsl hcyc
  obtain ⟨-, hU, -⟩ := ivk95_z_facts hz hq hsl hcyc
  have hqs := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 (by omega : 4 ≤ q) hsl
  have hperf : ⁅Ez z, Ez z⁆ = Ez z := Subgroup.isPerfect_iff.1 hqs.1
  have hne : Ez z ≠ ⊥ := by
    have := CFSG.LocalCores.isQuasisimple_nontrivial hqs
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  obtain ⟨k, _, _, hkcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hJ
  let π : SL(m, k) →* J :=
    e.symm.toMonoidHom.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m k)
  have hπ : IsCentralQuot π := by
    refine ⟨fun j => ?_, fun x => ?_⟩
    · obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective m k (e j)
      exact ⟨x, by simp [π, hx]⟩
    · have h1 : π x = 1 ↔ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m k x = 1 := by
        simp [π]
      rw [h1, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
  exact ivk95l_main hm (hkcard ▸ hodd) hπ hz hU hperf hne

end CFSG.GH74.GLS.IVK.Proofs2
