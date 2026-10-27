module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv2

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section A

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def M1K (a : PA7 L t E z) (K : Subgroup ↥(Cen a.ub)) : Subgroup ↥K :=
  (a.M₁.subgroupOf (Cen a.ub)).subgroupOf K

theorem M1_le_Cen (a : PA7 L t E z) : a.M₁ ≤ Cen a.ub := fun _ hx =>
  componentLayerOf_le _ (a.E₁_le (a.M₁_le hx))

theorem Cen_ne_top (hb : PAB G L t E W z) (a : PA5 L t E z) : Cen a.ub ≠ ⊤ := by
  intro h
  have hs := hb.setting.1.simple
  have hna := hb.setting.1.nonabelian
  have hc : center G = ⊥ := center_eq_bot_of_simple hs hna
  have : a.ub ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Cen a.ub := by rw [h]; trivial
    exact mem_Cen.1 this
  rw [hc, Subgroup.mem_bot] at this
  exact PA5.ub_ne_one a this

variable (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem M1Γ_le_K : a.M₁.subgroupOf (Cen a.ub) ≤ K := by
  intro x hx
  have h1 : (x : G) ∈ GorensteinWalter.componentLayerOf (Cen a.ub) := a.E₁_le (a.M₁_le hx)
  rw [inv_E hb a hK hcj hall] at h1
  obtain ⟨k, hk, hkx⟩ := h1
  have : k = x := Subtype.ext hkx
  rwa [← this]

@[expose] noncomputable def M1K_equiv : ↥(M1K a K) ≃* ↥a.M₁ :=
  (Subgroup.subgroupOfEquivOfLe (M1Γ_le_K hb a hK hcj hall)).trans
    (Subgroup.subgroupOfEquivOfLe (M1_le_Cen a))

theorem M1_qs : CFSG.IsQuasisimple ↥a.M₁ := by
  obtain ⟨f, hf, hker⟩ := a.M₁_cover
  have hP : Group.IsPerfect ↥a.M₁ := Subgroup.isPerfect_iff.2 a.M₁_perf
  haveI := s8_A6_simple
  exact (isQuasisimple_iff_of_surjective hP f hf hker).2
    (isQuasisimple_of_isSimpleGroup s8_A6_nonab).1

theorem M1K_qs : CFSG.IsQuasisimple ↥(M1K a K) :=
  isQuasisimple_of_mulEquiv (M1K_equiv hb a hK hcj hall).symm (M1_qs hb a hK hcj hall)

end A

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
