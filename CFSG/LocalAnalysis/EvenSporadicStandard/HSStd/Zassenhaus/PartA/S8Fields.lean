module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Swapped
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Swap2

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Fields

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (horb : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' →
    K' = K ∨ K' = cj (tG hb a.toPA6.toPA5) K)
  (hne : cj (tG hb a.toPA6.toPA5) K ≠ K)

include hb a hK horb hne

theorem sw_struct :
    (∀ x ∈ K, ∀ y ∈ K, x * (tG hb a.toPA6.toPA5 * y * (tG hb a.toPA6.toPA5)⁻¹) =
      (tG hb a.toPA6.toPA5 * y * (tG hb a.toPA6.toPA5)⁻¹) * x) ∧
    Nonempty (↥K ⧸ center ↥K ≃* ↥(JG hb a.toPA6.toPA5)) ∧
    (∀ z : ↥K, z ∈ center ↥K →
      tG hb a.toPA6.toPA5 * (z : ↥(Cen a.ub)) * (tG hb a.toPA6.toPA5)⁻¹ = (z : ↥(Cen a.ub))⁻¹ ∧
        (z : ↥(Cen a.ub)) ∈ cj (tG hb a.toPA6.toPA5) K) ∧
    (∀ k ∈ K, k * (tG hb a.toPA6.toPA5 * k * (tG hb a.toPA6.toPA5)⁻¹) ∈ JG hb a.toPA6.toPA5) :=
  swapped_structure (tG_mul_tG hb a.toPA6.toPA5) (JG_simple hb a.toPA6.toPA5)
    (JG_nonab hb a.toPA6.toPA5) (JG_perfect hb a.toPA6.toPA5)
    (fun j hj => JG_comm_t hb a.toPA6.toPA5 hj)
    (fun Q _ hQt hQ => JG_hHJ hb a.toPA6.toPA5 Q hQt hQ) hK hne
    (layer_eq_of_orbit hb a.toPA6.toPA5 hK horb)
    ((layer_eq_of_orbit hb a.toPA6.toPA5 hK horb) ▸ JG_le_layer hb a)

theorem sw_L1_A6 :
    Nonempty (↥(K.map (Cen a.ub).subtype) ⧸ center ↥(K.map (Cen a.ub).subtype) ≃*
      alternatingGroup (Fin 6)) := by
  obtain ⟨-, ⟨eq⟩, -, -⟩ := sw_struct hb a hK horb hne
  obtain ⟨eJ⟩ := s8_J_equiv a.Abar a.eAbar
  let e1 : ↥K ≃* ↥(K.map (Cen a.ub).subtype) :=
    Subgroup.equivMapOfInjective K (Cen a.ub).subtype (Cen a.ub).subtype_injective
  have hc : (center ↥K).map (e1 : ↥K →* ↥(K.map (Cen a.ub).subtype)) =
      center ↥(K.map (Cen a.ub).subtype) := Subgroup.map_center_eq e1
  exact ⟨((QuotientGroup.congr _ _ e1 hc).symm.trans eq).trans ((JG_equiv hb a.toPA6.toPA5).trans eJ)⟩

theorem sw_J_le :
    derivedIn a.Abar ≤ K.map (Cen a.ub).subtype ⊔ conjSub t (K.map (Cen a.ub).subtype) := by
  rw [← componentLayerOf_eq_sup hb a.toPA6.toPA5 hK horb]
  exact (a.J_E₁).trans a.E₁_le

theorem sw_perm : ∀ p ∈ Cen a.ub, (K.map (Cen a.ub).subtype).map (MulAut.conj p).toMonoidHom =
    K.map (Cen a.ub).subtype ∨ (K.map (Cen a.ub).subtype).map (MulAut.conj p).toMonoidHom =
      conjSub t (K.map (Cen a.ub).subtype) := by
  intro p hp
  have h := conj_map_subtype hb a.toPA6.toPA5 ⟨p, hp⟩ K
  have hcomp := isComponent_cj (⟨p, hp⟩ : ↥(Cen a.ub)) hK
  rcases horb _ hcomp with h1 | h1
  · left
    simpa [h1] using h
  · right
    rw [conjSub_map_subtype hb a.toPA6.toPA5]
    simpa [h1] using h

end Fields

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
