module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpLiftCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructCases
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSylow

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {G : Type} [Group G]

theorem ker_mk_vSub_le_center (v : G) :
    (QuotientGroup.mk' (vSub v)).ker ≤ center ↥(centralizer ({v} : Set G)) := by
  rw [QuotientGroup.ker_mk']
  exact vSub_le_center v

@[expose] def outerLift (v : G) (K : Subgroup (OuterSection v)) : Subgroup G :=
  (liftCore (QuotientGroup.mk' (vSub v)) K).map (centralizer ({v} : Set G)).subtype

theorem outerLift_le (v : G) (K : Subgroup (OuterSection v)) :
    outerLift v K ≤ centralizer ({v} : Set G) :=
  Subgroup.map_subtype_le _

theorem outerLift_subgroupOf (v : G) (K : Subgroup (OuterSection v)) :
    (outerLift v K).subgroupOf (centralizer ({v} : Set G)) =
      liftCore (QuotientGroup.mk' (vSub v)) K :=
  Subgroup.comap_map_eq_self_of_injective (centralizer ({v} : Set G)).subtype_injective _

noncomputable def outerLiftEquiv (v : G) (K : Subgroup (OuterSection v)) :
    ↥(liftCore (QuotientGroup.mk' (vSub v)) K) ≃* ↥(outerLift v K) :=
  Subgroup.equivMapOfInjective _ _ (centralizer ({v} : Set G)).subtype_injective

noncomputable def quotientCenterEquivOfEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isQuasisimple_outerLift (v : G) {K : Subgroup (OuterSection v)}
    (e : ↥K ≃* alternatingGroup (Fin 8)) : CFSG.IsQuasisimple ↥(outerLift v K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (outerLiftEquiv v K)
    (liftCore_isQuasisimple (QuotientGroup.mk'_surjective _) (ker_mk_vSub_le_center v) e)

theorem isCompIn_outerLift (v : G) {K : Subgroup (OuterSection v)} (hK : K.IsSubnormal)
    (e : ↥K ≃* alternatingGroup (Fin 8)) :
    IsCompIn (outerLift v K) (centralizer ({v} : Set G)) := by
  refine isCompIn_of_subnormal (outerLift_le v K) (isQuasisimple_outerLift v e) ?_
  rw [outerLift_subgroupOf]
  exact liftCore_isSubnormal _ hK

theorem nonempty_quotient_outerLift (v : G) {K : Subgroup (OuterSection v)}
    (e : ↥K ≃* alternatingGroup (Fin 8)) :
    Nonempty (↥(outerLift v K) ⧸ center ↥(outerLift v K) ≃* alternatingGroup (Fin 8)) := by
  have hK : ⁅K, K⁆ = K := commutator_eq_self_of_equiv_alternating_eight e
  have hKc : center ↥K = ⊥ := center_eq_bot_of_equiv_alt8' e
  exact ⟨(quotientCenterEquivOfEquiv (outerLiftEquiv v K)).symm.trans
    ((liftCore_quotientEquiv (QuotientGroup.mk'_surjective _) (ker_mk_vSub_le_center v) hK hKc).trans
      e)⟩

theorem commutator_outerLift_conj (v : G) {K : Subgroup (OuterSection v)}
    (e : ↥K ≃* alternatingGroup (Fin 8)) (g : G) (hg : g ∈ centralizer ({v} : Set G))
    (hc : ∀ a ∈ K, ∀ b ∈ PartA.cj (QuotientGroup.mk (⟨g, hg⟩ : ↥(centralizer ({v} : Set G))) :
      OuterSection v) K, a * b = b * a) :
    ⁅outerLift v K, (outerLift v K).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  set H := centralizer ({v} : Set G) with hH
  set φ := QuotientGroup.mk' (vSub v) with hφ
  set gH : ↥H := ⟨g, hg⟩ with hgH
  set D := liftCore φ K with hD
  have hK : ⁅K, K⁆ = K := commutator_eq_self_of_equiv_alternating_eight e
  have hperf : ⁅D, D⁆ = D := liftCore_perfect (QuotientGroup.mk'_surjective _)
    (ker_mk_vSub_le_center v) hK
  have hcomp : (MulAut.conj g).toMonoidHom.comp H.subtype =
      H.subtype.comp (MulAut.conj gH).toMonoidHom := by
    ext x
    rfl
  have hmap : (outerLift v K).map (MulAut.conj g).toMonoidHom =
      (D.map (MulAut.conj gH).toMonoidHom).map H.subtype := by
    rw [outerLift, Subgroup.map_map, Subgroup.map_map, hcomp]
  have hbot : ⁅D, D.map (MulAut.conj gH).toMonoidHom⁆ = ⊥ := by
    refine commutator_eq_bot_of_perfect hperf fun d hd e' he' => ?_
    obtain ⟨d', hd', rfl⟩ := he'
    have hdK : φ d ∈ K := liftCore_le_comap φ K hd
    have hdK' : φ d' ∈ K := liftCore_le_comap φ K hd'
    have hb : φ ((MulAut.conj gH).toMonoidHom d') ∈
        PartA.cj (QuotientGroup.mk gH : OuterSection v) K := by
      refine ⟨φ d', hdK', ?_⟩
      simp [hφ]
    have h1 : φ ⁅d, (MulAut.conj gH).toMonoidHom d'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc _ hdK _ hb
    exact ker_mk_vSub_le_center v (MonoidHom.mem_ker.2 h1)
  rw [hmap, outerLift, ← Subgroup.map_commutator, hbot, Subgroup.map_bot]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
