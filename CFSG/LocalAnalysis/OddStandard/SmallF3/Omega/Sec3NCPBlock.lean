module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutWRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.ComponentInitial.BlockAschbacherTheorem5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Main

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem asc82NonCommuteNonPocketed_of_walter12L2
    (h : Asc82Walter12L2) : Asc82NonCommuteNonPocketed := by
  intro G _ _ t L hS X hXC hXF hF hL g
  haveI : IsSimpleGroup G := hS.simple
  have huniv : ComponentAtCentralInvolutions X := h G t L hS X hXC hXF hF hL
  obtain ⟨x₀, hx₀, hXx₀⟩ := hXC.1
  have hXq : CFSG.Assembly.IsComponentOf X (centralizer ({x₀} : Set G)) :=
    (isComponentOf_iff_isComponent_subgroupOf hXx₀.1).2 hXx₀.2
  have hx₀X : x₀ ∈ centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXx₀.le ha)
  have hJ : IsUniversalComponent X := fun u hu hu2 =>
    (isComponentOf_iff_isComponent_subgroupOf (huniv u hu2 hu).1).2 (huniv u hu2 hu).2
  have hCeven : Even (Nat.card (centralizer (X : Set G))) := by
    have h1 : orderOf (⟨x₀, hx₀X⟩ : ↥(centralizer (X : Set G))) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hx₀
    have h2 := orderOf_dvd_natCard (⟨x₀, hx₀X⟩ : ↥(centralizer (X : Set G)))
    rw [h1] at h2
    exact even_iff_two_dvd.2 h2
  exact universal_rank_two_component_commutator_ne_bot (sec4_nonabelian hS.toSec3Setting)
    hXq.2.2 (aor_two_le_pRank_of_nonPocketed hXF hF hL) hCeven hJ g

end CFSG.OddStandard.SmallF3.Omega
