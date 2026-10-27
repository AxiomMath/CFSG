module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Cpe2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Z

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (horb : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' →
    K' = K ∨ K' = cj (tG hb a.toPA6.toPA5) K)
  (hne : cj (tG hb a.toPA6.toPA5) K ≠ K)

include hb a hK horb hne

theorem exists_PA8_of_swapped : Nonempty (PA8 L t E z) := by
  have hle1 : K.map (Cen a.ub).subtype ≤ GorensteinWalter.componentLayerOf (Cen a.ub) := by
    rw [componentLayerOf_eq_sup hb a.toPA6.toPA5 hK horb]; exact le_sup_left
  have hle2 : conjSub t (K.map (Cen a.ub).subtype) ≤
      GorensteinWalter.componentLayerOf (Cen a.ub) := by
    rw [componentLayerOf_eq_sup hb a.toPA6.toPA5 hK horb]; exact le_sup_right
  refine ⟨{ toPA7 := a
            L₁ := K.map (Cen a.ub).subtype
            L₁_comp := isComponentOf_map_subtype _ hK
            L₁_ne := ?_
            L₁_comm := ?_
            E_eq := componentLayerOf_eq_sup hb a.toPA6.toPA5 hK horb
            L₁_A6 := sw_L1_A6 hb a hK horb hne
            Z_le := sw_Z_le hb a hK horb hne
            perm := sw_perm hb a hK horb hne
            J_le := sw_J_le hb a hK horb hne
            CPE_eq := sw_CPE_eq hb a hK horb hne
            u₁_CPE := ?_ }⟩
  · rw [conjSub_map_subtype hb a.toPA6.toPA5]
    intro h
    exact hne (Subgroup.map_injective (Cen a.ub).subtype_injective h)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨hc, -⟩ := sw_struct hb a hK horb hne
    have := congrArg Subtype.val (hc x hx y hy)
    have h : (x : G) * (t * (y : G) * t⁻¹) = (t * (y : G) * t⁻¹) * (x : G) := by
      simpa [tG] using this
    exact h
  · intro hd
    have hu1E := sw_u1_cent_layer hb a hK horb hne hd
    exact ⟨Subgroup.mem_centralizer_iff.2 fun x hx => (hu1E x (hle1 hx)).symm,
      Subgroup.mem_centralizer_iff.2 fun x hx => (hu1E x (hle2 hx)).symm⟩

end Main

@[expose] def S8Invariant : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G)
    (hb : PAB G L t E W z) (a : PA7 L t E z) (K : Subgroup ↥(Cen a.ub)), IsComponent K →
    cj (tG hb a.toPA6.toPA5) K = K → (∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K) →
    False

theorem s8_of_invariant (h : S8Invariant) : StepS8 := by
  intro G _ _ L t E W z hb a
  obtain ⟨K, hK, horb⟩ := exists_orbit hb a
  by_cases hcj : cj (tG hb a.toPA6.toPA5) K = K
  · exfalso
    exact h G L t E W z hb a K hK hcj (fun K' hK' => (horb K' hK').elim id fun h => h.trans hcj)
  · exact exists_PA8_of_swapped hb a hK horb hcj

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
