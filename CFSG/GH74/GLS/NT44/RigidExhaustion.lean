module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.Stage1.Thm4.P92Pump
import CFSG.GH74.GLS.Bg.Iii2.CMPU

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
open CFSG.GH74.GLS.Stage1.Thm4.P92 CFSG.GH74.GLS.Bg.Iii2.CMEngine

theorem rigid_pump_exhaustion
    {G : Type} [Group G] [Finite G] {fullQ : Type} [Group fullQ] {x t : G}
    (J : Subgroup G → Subgroup G)
    (hxY : x ∈ centralizer ({t} : Set G))
    (hJ : ∀ K ∈ RigidSet fullQ x, PumpUpLT 2 x K t (J K))
    (hcard : (RigidSet fullQ t).ncard ≤ (RigidSet fullQ x).ncard) :
    (Set.InjOn J (RigidSet fullQ x)) ∧
      (∀ K ∈ RigidSet fullQ x, IsRigidOfType fullQ t (J K)) ∧
      (RigidSet fullQ t = J '' RigidSet fullQ x) ∧
      (∀ K ∈ RigidSet fullQ x,
        x ∈ normalizer (J K : Set G) ∧
          (∀ Lambda : Subgroup G,
            IsLam x t K Lambda →
              Lambda ≤ J K ∧ bar t Lambda = bar t (J K))) := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hstep : ∀ K ∈ RigidSet fullQ x, ∃ Λ : Subgroup G,
      StepData x t hxY K (J K) Λ := by
    intro K hK
    exact exists_stepData' hK.1 (hJ K hK) hxY
  choose! LambdaF hLambdaF using hstep
  have hrig : ∀ K ∈ RigidSet fullQ x, IsRigidOfType fullQ t (J K) := by
    intro K hK
    exact isRigidOfType_of_pumpUpLT hK (hJ K hK)
  have hinj : Set.InjOn J (RigidSet fullQ x) := by
    intro K hK K' hK' hJK
    by_contra hne
    have h2 : StepData x t hxY K' (J K) (LambdaF K') := by
      rw [hJK]
      exact hLambdaF K' hK'
    exact bar_lam_ne_of_ne (hK.1.1.2.2) (hK'.1.1.2.2) hne
      (hLambdaF K hK).lam (hLambdaF K' hK').lam
      ((hLambdaF K hK).bar_eq_of_eq h2)
  have hsub : J '' RigidSet fullQ x ⊆ RigidSet fullQ t := by
    rintro _ ⟨K, hK, rfl⟩
    exact hrig K hK
  have hncard : (J '' RigidSet fullQ x).ncard = (RigidSet fullQ x).ncard :=
    hinj.ncard_image
  have hEq : J '' RigidSet fullQ x = RigidSet fullQ t :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hncard]; exact hcard) (Set.toFinite _)
  have hvert : ∀ K ∈ RigidSet fullQ x, x ∈ normalizer (J K : Set G) := by
    intro K hK
    by_contra hx
    have hJ'rr : IsRigidOfType fullQ t (cmap x (J K)) := by
      have h := isRigidOfType_conj (hrig K hK) x
      rwa [conj_fix_of_mem_centralizer hxY] at h
    have hmem : cmap x (J K) ∈ J '' RigidSet fullQ x := by
      rw [hEq]
      exact hJ'rr
    obtain ⟨K', hK', hJK'⟩ := hmem
    have hne : K ≠ K' := by
      rintro rfl
      exact hx (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hJK'.symm)
    have h2 : StepData x t hxY K' (cmap x (J K)) (LambdaF K') := by
      rw [← hJK']
      exact hLambdaF K' hK'
    exact bar_lam_ne_of_ne (hK.1.1.2.2) (hK'.1.1.2.2) hne
      (hLambdaF K hK).lam (hLambdaF K' hK').lam
      ((hLambdaF K hK).bar_eq_of_cmap hK.1.1.1 hx h2)
  have hvert_lam : ∀ K ∈ RigidSet fullQ x,
      x ∈ normalizer (J K : Set G) ∧
        (∀ Lambda : Subgroup G, IsLam x t K Lambda →
          Lambda ≤ J K ∧ bar t Lambda = bar t (J K)) := by
    intro K hK
    refine ⟨hvert K hK, ?_⟩
    intro Lambda hLambda
    have hLamEq : Lambda = LambdaF K :=
      hLambda.layer.symm.trans (hLambdaF K hK).lam.layer
    have hbar : bar t (LambdaF K) = bar t (J K) :=
      ((hLambdaF K hK).cases.resolve_right (fun h => h.1 (hvert K hK))).2
    have hle : Lambda ≤ J K := by
      rw [hLamEq]
      exact lam_le_of_bar_le (hLambdaF K hK).lam (hrig K hK).1.1.2.2 hbar.le
    refine ⟨hle, ?_⟩
    rw [hLamEq]
    exact hbar
  exact ⟨hinj, hrig, hEq.symm, hvert_lam⟩

end CFSG.GH74.GLS.NT44

end
