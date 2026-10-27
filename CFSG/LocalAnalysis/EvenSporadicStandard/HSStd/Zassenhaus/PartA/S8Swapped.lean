module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Gamma

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem conjSub_map_subtype (hb : PAB G L t E W z) (a : PA5 L t E z)
    (K : Subgroup ↥(Cen a.ub)) :
    conjSub t (K.map (Cen a.ub).subtype) = (cj (tG hb a) K).map (Cen a.ub).subtype := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨tG hb a * y * (tG hb a)⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, tG]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(y : G), ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, tG]

theorem isComponentOf_map_subtype (H : Subgroup G) {K : Subgroup ↥H} (hK : IsComponent K) :
    GorensteinWalter.IsComponentOf (K.map H.subtype) H := by
  have hXH : K.map H.subtype ≤ H := Subgroup.map_subtype_le K
  rw [gw_isComponentOf_iff hXH]
  have e : (K.map H.subtype).subgroupOf H = K :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
  rw [e]
  exact hK

theorem layer_eq_of_orbit (hb : PAB G L t E W z) (a : PA5 L t E z) {K : Subgroup ↥(Cen a.ub)}
    (hK : IsComponent K)
    (horb : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K ∨ K' = cj (tG hb a) K) :
    layer ↥(Cen a.ub) = K ⊔ cj (tG hb a) K := by
  apply le_antisymm
  · refine sSup_le fun K' hK' => ?_
    rcases horb K' hK' with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (component_le_layer hK) (component_le_layer (isComponent_cj _ hK))

theorem componentLayerOf_eq_sup (hb : PAB G L t E W z) (a : PA5 L t E z)
    {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
    (horb : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K ∨ K' = cj (tG hb a) K) :
    GorensteinWalter.componentLayerOf (Cen a.ub) =
      K.map (Cen a.ub).subtype ⊔ conjSub t (K.map (Cen a.ub).subtype) := by
  rw [componentLayerOf_eq, layer_eq_of_orbit hb a hK horb, Subgroup.map_sup,
    conjSub_map_subtype hb a]

theorem conj_map_subtype (hb : PAB G L t E W z) (a : PA5 L t E z) (g : ↥(Cen a.ub))
    (K : Subgroup ↥(Cen a.ub)) :
    (K.map (Cen a.ub).subtype).map (MulAut.conj (g : G)).toMonoidHom =
      (cj g K).map (Cen a.ub).subtype := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨g * y * g⁻¹, ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(y : G), ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]

theorem cj_eq_of_commute {Γ : Type*} [Group Γ] {t : Γ} (ht : t * t = 1) {K : Subgroup Γ}
    (h : ∀ k ∈ K, t * k = k * t) : cj t K = K := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (MulAut.conj t).toMonoidHom y = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [h y hy]; group
    rw [this]; exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h x hx]; group

theorem centralizes_sup_of_mem {Γ : Type*} [Group Γ] {K K' : Subgroup Γ}
    (hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) {k : Γ} (hk : k ∈ K) (hkK' : k ∈ K')
    (hkc : ∀ x ∈ K, k * x = x * k) : ∀ x ∈ K ⊔ K', k * x = x * k := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hx
  calc k * (a * b) = (k * a) * b := by rw [mul_assoc]
    _ = (a * k) * b := by rw [hkc a ha]
    _ = a * (k * b) := by rw [mul_assoc]
    _ = a * (b * k) := by rw [(hcomm k hk b hb)]
    _ = a * b * k := by rw [mul_assoc]

end Transfer

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
