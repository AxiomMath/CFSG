module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGOutZetaBDefs
public import CFSG.Sporadic.Recognition.CoverTransfer
public import CFSG.GroupTheory.PerfectCoverProduct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43
open scoped commutatorElement

theorem zetaLift_holds : ZetaLift := by
  intro S E _ _ q _ hker hcomm s hP hwg eh heh
  let e : Fin 2 → E := zCanon eh
  have hzw : ∀ i, zW i ∈ commutator (FreeGroup (Fin 2)) := fun i =>
    mk_commWords_mem_commutator (coverPairs i)
  have hqe : ∀ i, q (e i) = s i := by
    intro i
    have hcomp : q.comp (FreeGroup.lift eh) = FreeGroup.lift (fun j => q (eh j)) :=
      FreeGroup.ext_hom _ _ fun j => by simp
    show (q.comp (FreeGroup.lift eh)) (zW i) = s i
    rw [hcomp, show (fun j => q (eh j)) = s from funext heh]
    exact hwg i
  have hcen : ∀ i, (eh i)⁻¹ * e i ∈ Subgroup.center E := by
    intro i
    refine hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hqe i, heh i]
    exact inv_mul_cancel _
  have heval : ∀ i, FreeGroup.lift e (zW i) = e i := by
    intro i
    show FreeGroup.lift e (zW i) = FreeGroup.lift eh (zW i)
    exact CFSG.Sporadic.Recognition.CoverTransfer.lift_eq_lift_of_mem_commutator hcen (hzw i)
  have hrel : ∀ r ∈ coverRelators (wordSet rels) zW, FreeGroup.lift e r = 1 := by
    refine lift_coverRelators_eq_one_iff.mpr ⟨?_, heval⟩
    intro i r hr
    have hqr : q (FreeGroup.lift e r) = 1 := by
      have hcomp : q.comp (FreeGroup.lift e) = FreeGroup.lift (fun j => q (e j)) :=
        FreeGroup.ext_hom _ _ fun j => by simp
      show (q.comp (FreeGroup.lift e)) r = 1
      rw [hcomp, show (fun j => q (e j)) = s from funext hqe]
      exact hP.lift_eq_one hr
    have hz : FreeGroup.lift e r ∈ Subgroup.center E := hker (MonoidHom.mem_ker.mpr hqr)
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz (e i))
  let lam : ZetaCover →* E := PresentedGroup.toGroup hrel
  have hlam_of : ∀ i, lam (PresentedGroup.of i) = e i := fun i =>
    PresentedGroup.toGroup.of hrel
  have hcomp_lam : q.comp lam = coverMap (w := zW) hP hwg := by
    refine PresentedGroup.ext fun i => ?_
    simp only [MonoidHom.comp_apply, hlam_of i, hqe i, coverMap_of]
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro i
    simpa [e] using hlam_of i
  · intro p
    show (q.comp lam) p = coverMap (w := zW) hP hwg p
    rw [hcomp_lam]
  · rw [← MonoidHom.range_eq_top]
    have hsur : Function.Surjective (q.comp lam) := by
      rw [hcomp_lam]
      exact coverMap_surjective hP hwg
    have htop : commutator E ≤ lam.range := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨p, hp⟩ := hsur (q x)
      obtain ⟨p', hp'⟩ := hsur (q y)
      have hx : x = lam p * ((lam p)⁻¹ * x) := by group
      have hy : y = lam p' * ((lam p')⁻¹ * y) := by group
      have hcx : (lam p)⁻¹ * x ∈ q.ker := by
        have hpx : q (lam p) = q x := hp
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpx]
        exact inv_mul_cancel _
      have hcy : (lam p')⁻¹ * y ∈ q.ker := by
        have hpy : q (lam p') = q y := hp'
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpy]
        exact inv_mul_cancel _
      rw [hx, hy, CFSG.GroupTheory.PerfectCover.commutatorElement_mul_mul_of_mem_center
        (hker hcx) (hker hcy)]
      exact Subgroup.commutator_le_of_le (K := lam.range) le_rfl le_rfl
        (Subgroup.commutator_mem_commutator (MonoidHom.mem_range.mpr ⟨p, rfl⟩)
          (MonoidHom.mem_range.mpr ⟨p', rfl⟩))
    exact le_antisymm le_top (hcomm ▸ htop)

end CFSG.OddStandard.SmallF3.Omega
