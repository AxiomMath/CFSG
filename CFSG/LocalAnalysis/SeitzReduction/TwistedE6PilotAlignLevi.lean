module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignLeviWeyl
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignLeviBruhat

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_mono perfectCore_le le_perfectCore_of_perfect
  perfectCore_perfect)

local instance twistedE6PilotAlignLeviNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotAlignLeviNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotAlignLeviNeZeroE6' : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

variable {K : Type} [Field K]

section Levi

theorem relLevi_le_adjointGroup (I : Finset (Fin Tag.F4.rank)) :
    relLevi K I ≤ adjointGroup TwistTag.E6.tag K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem relLevi_le_subsystemGroup {I : Finset (Fin Tag.F4.rank)}
    {S : Set (Fin TwistTag.E6.tag.rank)} (hS : ∀ j ∈ relNodeSet I, j ∈ S) :
    relLevi K I ≤ subsystemGroup TwistTag.E6.tag K S := by
  rw [relLevi, ← F4Pilot.closure_xUnit_yUnit_eq_rootSpan]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨j, hj, c, h⟩
  exact ⟨j, hS j hj, c, h⟩

theorem graphFixedRootGroup_le_adjointGroup' (σ : K →+* K) :
    graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup TwistTag.E6.tag K :=
  (graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left

theorem commutator_relLevi_eq {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    (I : Finset (Fin Tag.F4.rank)) : ⁅relLevi K I, relLevi K I⁆ = relLevi K I := by
  obtain ⟨c, -, hc⟩ := F4Pilot.exists_mem_orderOf_eq_natCard hA
  exact F4Pilot.commutator_rootSpan_signedSimpleRoots_eq
    (F4Pilot.ne_one_and_sq_ne_one_of_three_le_orderOf (hc ▸ hA)).2 _

theorem relLevi_le_inf_centralizer (A : Subgroup Kˣ) (I : Finset (Fin Tag.F4.rank)) :
    relLevi K I ≤ adjointGroup TwistTag.E6.tag K ⊓
      centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K)) :=
  le_inf (relLevi_le_adjointGroup I) (relLevi_le_centralizer_relLeviTorus A I)

end Levi

section Main

theorem perfectCore_le_relLevi_of_le {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) {H : Subgroup (ModGL TwistTag.E6.tag K)}
    (hH : H ≤ adjointGroup TwistTag.E6.tag K ⊓
      centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))) :
    perfectCore H ≤ relLevi K I :=
  perfectCore_le_rootSpan_of_forall_conj_eq_of_comm (relTupleSet A I)
    (relNodeSet I : Set (Fin TwistTag.E6.tag.rank))
    (fun _ hα _ => coeff_eq_zero_of_mem_toralSetKernel_relTupleSet hA hI hα)
    (fun _ ha => apply_eq_one_of_mem_relTupleSet ha)
    (fun _ _ hw₁ hw₂ => smul_comm_apply_eq_of_mem_relTupleSet hA hI hw₁ hw₂)
    fun g hg => ⟨(mem_inf.1 (hH hg)).1, fun a ha => by
      obtain ⟨B, hB, rfl⟩ := ha
      have h := mem_centralizer_iff.1 (mem_inf.1 (hH hg)).2 _
        (rootDiagUnit_relTuple_mem_relLeviTorus hB)
      rw [h, mul_inv_cancel_right]⟩

theorem perfectCore_inf_centralizer_relLeviTorus {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) :
    perfectCore (adjointGroup TwistTag.E6.tag K ⊓
        centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))) =
      relLevi K I :=
  le_antisymm (perfectCore_le_relLevi_of_le hA hI le_rfl)
    (le_perfectCore_of_perfect (relLevi_le_inf_centralizer A I) (commutator_relLevi_eq hA I))

theorem perfectCore_inf_centralizer_relLeviTorus_of_le {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) {D : Subgroup (ModGL TwistTag.E6.tag K)}
    (hD : D ≤ adjointGroup TwistTag.E6.tag K) (hLD : relLevi K I ≤ D) :
    perfectCore (D ⊓ centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))) =
      relLevi K I :=
  le_antisymm (perfectCore_le_relLevi_of_le hA hI (inf_le_inf_right _ hD))
    (le_perfectCore_of_perfect (le_inf hLD (relLevi_le_centralizer_relLeviTorus A I))
      (commutator_relLevi_eq hA I))

theorem perfectCore_inf_centralizer_relLeviTorus_X {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) (hIX : I ⊆ {1, 2, 3}) :
    perfectCore (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))) =
      relLevi K I := by
  refine perfectCore_inf_centralizer_relLeviTorus_of_le hA hI
    (Subgroup.closure_le _ |>.2 ?_) (relLevi_le_subsystemGroup fun j hj => ?_)
  · rintro _ ⟨i, -, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]
  · have h : ∀ j : Fin Tag.E6.rank, e6IndexToF4 j ∈ ({1, 2, 3} : Finset (Fin Tag.F4.rank)) →
        j ≠ 1 := by decide
    exact h j (hIX (mem_relNodeSet.1 hj))

theorem perfectCore_inf_centralizer_relLeviTorus_Y {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) (hIY : I ⊆ {0, 1, 2}) :
    perfectCore (subsystemGroup TwistTag.E6.tag K C2E6Std.setD ⊓
        centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))) =
      relLevi K I := by
  refine perfectCore_inf_centralizer_relLeviTorus_of_le hA hI
    (Subgroup.closure_le _ |>.2 ?_) (relLevi_le_subsystemGroup fun j hj => ?_)
  · rintro _ ⟨i, -, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]
  · have h : ∀ j : Fin Tag.E6.rank, e6IndexToF4 j ∈ ({0, 1, 2} : Finset (Fin Tag.F4.rank)) →
        j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
    exact h j (hIY (mem_relNodeSet.1 hj))

theorem perfectCore_inf_centralizer_relLeviTorus_of_le_C0 [Finite K] {σ : K →+* K}
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A) {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2)
    {D : Subgroup (ModGL TwistTag.E6.tag K)} (hD : D ≤ graphFixedRootGroup TwistTag.E6 K σ)
    (hLD : relLevi K I ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤ D) :
    perfectCore (D ⊓ centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))) =
      perfectCore (relLevi K I ⊓ graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  refine le_antisymm (le_perfectCore_of_perfect (le_inf ?_ ?_) (perfectCore_perfect _))
    (perfectCore_mono (le_inf hLD (inf_le_left.trans (relLevi_le_centralizer_relLeviTorus A I))))
  · exact perfectCore_le_relLevi_of_le hA hI
      (inf_le_inf_right _ (hD.trans (graphFixedRootGroup_le_adjointGroup' σ)))
  · exact (perfectCore_le _).trans (inf_le_left.trans hD)

theorem perfectCore_C0_inf_centralizer_relLeviTorus [Finite K] (σ : K →+* K)
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A) {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) :
    perfectCore (graphFixedRootGroup TwistTag.E6 K σ ⊓
        centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K))) =
      perfectCore (relLevi K I ⊓ graphFixedRootGroup TwistTag.E6 K σ) :=
  perfectCore_inf_centralizer_relLeviTorus_of_le_C0 hA hI le_rfl inf_le_right

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
