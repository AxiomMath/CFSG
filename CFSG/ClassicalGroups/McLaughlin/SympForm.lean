module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination

public section

universe u v

namespace CFSG.ClassicalGroups.McLaughlin

open Module

section Basic

variable {K : Type v} [Field K]

variable {V : Type u} [AddCommGroup V] [Module K V]

private def rootMap (δ : V → Dual K V) (a : V) (c : K) : V →ₗ[K] V :=
  1 + c • (δ a).smulRight a

private theorem rootMap_apply (δ : V → Dual K V) (a : V) (c : K) (x : V) :
    rootMap δ a c x = x + (c * δ a x) • a := by
  simp only [rootMap, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, smul_smul]

private abbrev Pres (δ : V → Dual K V) (g : V →ₗ[K] V) : Prop :=
  ∀ x y, δ (g x) y = 0 ↔ ∃ z, δ x z = 0 ∧ g z = y

private abbrev Good (δ : V → Dual K V) (β : LinearMap.BilinForm K V) (g : V →ₗ[K] V) : Prop :=
  Pres δ g ∧ Function.Surjective g ∧ ∀ x y, β (g x) (g y) = β x y

private abbrev SympHyp (δ : V → Dual K V) : Prop :=
  (∀ v, v ≠ 0 → δ v ≠ 0) ∧ (∀ v, δ v v = 0) ∧ (∀ v w, δ v w = 0 ↔ δ w v = 0) ∧
    ∀ (a : V) (c : K), Pres δ (rootMap δ a c)

private abbrev Concl (δ : V → Dual K V) (β : LinearMap.BilinForm K V) : Prop :=
  β.Nondegenerate ∧ (∀ x, β x x = 0) ∧ ∀ v w, v ≠ 0 → (β v w = 0 ↔ δ v w = 0)

private theorem bilin_anti {B : LinearMap.BilinForm K V} (hB : ∀ x, B x x = 0) (x y : V) :
    B x y + B y x = 0 := by
  have h := hB (x + y)
  simp only [map_add, LinearMap.add_apply, hB x, hB y, zero_add, add_zero] at h
  linear_combination h

private theorem pres_comp {δ : V → Dual K V} {g h : V →ₗ[K] V} (hg : Pres δ g) (hh : Pres δ h) :
    Pres δ (g ∘ₗ h) := by
  intro x y
  rw [LinearMap.comp_apply, hg]
  constructor
  · rintro ⟨z, hz, hgz⟩
    obtain ⟨w, hw, rfl⟩ := (hh x z).1 hz
    exact ⟨w, hw, hgz⟩
  · rintro ⟨w, hw, hgy⟩
    exact ⟨h w, (hh x (h w)).2 ⟨w, hw, rfl⟩, hgy⟩

private theorem good_comp {δ : V → Dual K V} {β : LinearMap.BilinForm K V} {g h : V →ₗ[K] V}
    (hg : Good δ β g) (hh : Good δ β h) : Good δ β (g ∘ₗ h) := by
  refine ⟨pres_comp hg.1 hh.1, hg.2.1.comp hh.2.1, fun x y => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hg.2.2, hh.2.2]

private theorem rootMap_neg_comp {δ : V → Dual K V} (h1 : ∀ v, δ v v = 0) (a : V) (c : K)
    (x : V) : rootMap δ a c (rootMap δ a (-c) x) = x := by
  simp only [rootMap_apply, map_add, map_smul, h1, smul_eq_mul, mul_zero, add_zero]
  module

private theorem rootMap_surj {δ : V → Dual K V} (h1 : ∀ v, δ v v = 0) (a : V) (c : K) :
    Function.Surjective (rootMap δ a c) :=
  fun y => ⟨rootMap δ a (-c) y, rootMap_neg_comp h1 a c y⟩

private theorem good_of_prop {δ : V → Dual K V} {β : LinearMap.BilinForm K V}
    (hβ : ∀ x, β x x = 0) (h1 : ∀ v, δ v v = 0) {a : V} (c κ : K)
    (hκ : ∀ x, δ a x = κ * β a x) (hP : Pres δ (rootMap δ a c)) :
    Good δ β (rootMap δ a c) := by
  refine ⟨hP, rootMap_surj h1 a c, fun x y => ?_⟩
  simp only [rootMap_apply, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, hκ, hβ, mul_zero, add_zero]
  linear_combination (c * κ * β a y) * bilin_anti hβ x a

private theorem prop_of_ker {X : Type*} [AddCommGroup X] [Module K X] {φ ψ : X →ₗ[K] K}
    (hφ : ∃ w, φ w ≠ 0) (h : ∀ x, φ x = 0 → ψ x = 0) : ∃ c : K, ∀ x, ψ x = c * φ x := by
  obtain ⟨w, hw⟩ := hφ
  refine ⟨ψ w / φ w, fun x => ?_⟩
  have hx : φ (x - (φ x / φ w) • w) = 0 := by
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hw, sub_self]
  have h2 := h _ hx
  rw [map_sub, map_smul, smul_eq_mul] at h2
  linear_combination h2

private structure HypPair (δ : V → Dual K V) (e f : V) : Prop where
  ee : δ e e = 0
  ff : δ f f = 0
  ef : δ e f ≠ 0
  fe : δ f e ≠ 0

private def Wp (δ : V → Dual K V) (e f : V) : Submodule K V :=
  LinearMap.ker (δ e) ⊓ LinearMap.ker (δ f)

private theorem mem_Wp {δ : V → Dual K V} {e f x : V} :
    x ∈ Wp δ e f ↔ δ e x = 0 ∧ δ f x = 0 := by
  simp only [Wp, Submodule.mem_inf, LinearMap.mem_ker]

private def qmap (δ : V → Dual K V) (e f : V) : V →ₗ[K] V :=
  (δ f e)⁻¹ • (δ f).smulRight e + (δ e f)⁻¹ • (δ e).smulRight f

private theorem qmap_apply (δ : V → Dual K V) (e f x : V) :
    qmap δ e f x = ((δ f e)⁻¹ * δ f x) • e + ((δ e f)⁻¹ * δ e x) • f := by
  simp only [qmap, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    smul_smul]

private def pmap (δ : V → Dual K V) (e f : V) : V →ₗ[K] V :=
  LinearMap.id - qmap δ e f

private theorem pmap_apply (δ : V → Dual K V) (e f x : V) :
    pmap δ e f x = x - qmap δ e f x := by
  simp [pmap]

private theorem delta_e_qmap {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) (x : V) :
    δ e (qmap δ e f x) = δ e x := by
  rw [qmap_apply, map_add, map_smul, map_smul, P.ee, smul_zero, zero_add, smul_eq_mul]
  have := P.ef
  field_simp

private theorem delta_f_qmap {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) (x : V) :
    δ f (qmap δ e f x) = δ f x := by
  rw [qmap_apply, map_add, map_smul, map_smul, P.ff, smul_zero, add_zero, smul_eq_mul]
  have := P.fe
  field_simp

private theorem pmap_mem {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) (x : V) :
    pmap δ e f x ∈ Wp δ e f := by
  rw [mem_Wp, pmap_apply, map_sub, map_sub, delta_e_qmap P, delta_f_qmap P]
  exact ⟨sub_self _, sub_self _⟩

private theorem qmap_of_mem {δ : V → Dual K V} {e f u : V} (hu : u ∈ Wp δ e f) :
    qmap δ e f u = 0 := by
  obtain ⟨h1, h2⟩ := mem_Wp.1 hu
  rw [qmap_apply, h1, h2]
  simp

private theorem pmap_of_mem {δ : V → Dual K V} {e f u : V} (hu : u ∈ Wp δ e f) :
    pmap δ e f u = u := by
  rw [pmap_apply, qmap_of_mem hu, sub_zero]

private theorem qmap_e {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) :
    qmap δ e f e = e := by
  rw [qmap_apply, P.ee, inv_mul_cancel₀ P.fe]
  simp

private theorem qmap_f {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) :
    qmap δ e f f = f := by
  rw [qmap_apply, P.ff, inv_mul_cancel₀ P.ef]
  simp

private theorem pmap_e {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) :
    pmap δ e f e = 0 := by
  rw [pmap_apply, qmap_e P, sub_self]

private theorem pmap_f {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) :
    pmap δ e f f = 0 := by
  rw [pmap_apply, qmap_f P, sub_self]

private theorem delta_qmap_of_mem {δ : V → Dual K V} {e f : V}
    (hD : (∀ v w, δ v w = 0 ↔ δ w v = 0)) {u : V} (hu : u ∈ Wp δ e f) (x : V) :
    δ u (qmap δ e f x) = 0 := by
  obtain ⟨h1, h2⟩ := mem_Wp.1 hu
  have he : δ u e = 0 := (hD e u).1 h1
  have hf : δ u f = 0 := (hD f u).1 h2
  rw [qmap_apply, map_add, map_smul, map_smul, he, hf, smul_zero, smul_zero, add_zero]

private def pW {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) : V →ₗ[K] Wp δ e f :=
  LinearMap.codRestrict (Wp δ e f) (pmap δ e f) (fun x => pmap_mem P x)

private theorem pW_coe {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) (y : Wp δ e f) :
    pW P (y : V) = y :=
  Subtype.ext (pmap_of_mem y.2)

private def glue {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (c : K) : LinearMap.BilinForm K V :=
  c • (((δ e).smulRight (δ f) - (δ f).smulRight (δ e) : V →ₗ[K] Dual K V) :
      LinearMap.BilinForm K V) + β'.compl₁₂ (pW P) (pW P)

private theorem glue_apply {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (c : K) (x y : V) :
    glue P β' c x y = c * (δ e x * δ f y - δ f x * δ e y) + β' (pW P x) (pW P y) := by
  simp only [glue, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, LinearMap.compl₁₂_apply, smul_eq_mul]

private theorem glue_alt {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (hβ' : ∀ x, β' x x = 0) (c : K) (x : V) :
    glue P β' c x x = 0 := by
  rw [glue_apply, hβ' (pW P x)]
  ring

private theorem pW_e {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) : pW P e = 0 :=
  Subtype.ext (pmap_e P)

private theorem pW_f {δ : V → Dual K V} {e f : V} (P : HypPair δ e f) : pW P f = 0 :=
  Subtype.ext (pmap_f P)

private theorem glue_nondeg {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (hnd : β'.Nondegenerate)
    (hβ' : ∀ x, β' x x = 0) {c : K} (hc : c ≠ 0) : (glue P β' c).Nondegenerate := by
  have hsep : LinearMap.SeparatingLeft (glue P β' c) := by
    intro x hx
    have h1 : pW P x = 0 := by
      refine hnd.1 _ (fun y' => ?_)
      have h := hx (y' : V)
      simp only [glue_apply, (mem_Wp.1 y'.2).1, (mem_Wp.1 y'.2).2, pW_coe P y', mul_zero,
        sub_self, zero_add] at h
      exact h
    have hpx : pmap δ e f x = 0 := congrArg Subtype.val h1
    have hex : δ e x = 0 := by
      have h := hx e
      simp only [glue_apply, P.ee, pW_e P, map_zero, mul_zero, sub_zero, add_zero] at h
      have h' : δ e x * δ f e = 0 := (mul_eq_zero.1 h).resolve_left hc
      exact (mul_eq_zero.1 h').resolve_right P.fe
    have hfx : δ f x = 0 := by
      have h := hx f
      simp only [glue_apply, P.ff, pW_f P, map_zero, mul_zero, zero_sub, add_zero] at h
      have h' : c * (δ f x * δ e f) = 0 := by linear_combination -h
      have h'' : δ f x * δ e f = 0 := (mul_eq_zero.1 h').resolve_left hc
      exact (mul_eq_zero.1 h'').resolve_right P.ef
    have hq : qmap δ e f x = 0 := by
      rw [qmap_apply, hex, hfx, mul_zero, mul_zero, zero_smul, zero_smul, add_zero]
    rw [pmap_apply, hq, sub_zero] at hpx
    exact hpx
  refine ⟨hsep, fun y hy => ?_⟩
  apply hsep y
  intro x
  have h := bilin_anti (glue_alt P β' hβ' c) y x
  rw [hy x, add_zero] at h
  exact h

private theorem transport {δ : V → Dual K V} {β : LinearMap.BilinForm K V} {g : V →ₗ[K] V}
    (hg : Good δ β g) {x : V} (hx : ∀ y, δ x y = 0 ↔ β x y = 0) (y : V) :
    δ (g x) y = 0 ↔ β (g x) y = 0 := by
  rw [hg.1 x y]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hg.2.2 x z]
    exact (hx z).1 hz
  · intro h
    obtain ⟨z, rfl⟩ := hg.2.1 y
    rw [hg.2.2 x z] at h
    exact ⟨z, (hx z).2 h, rfl⟩

private theorem kr_of_prop {δ : V → Dual K V} {β : LinearMap.BilinForm K V} {a : V} {κ : K}
    (hκ0 : κ ≠ 0) (hκ : ∀ x, δ a x = κ * β a x) (x : V) : δ a x = 0 ↔ β a x = 0 := by
  rw [hκ x]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_left hκ0, fun h => by rw [h, mul_zero]⟩

private theorem mem_rootMap_iff {δ : V → Dual K V} {W : Submodule K V} {a : V} (ha : a ∈ W)
    (c : K) (z : V) : rootMap δ a c z ∈ W ↔ z ∈ W := by
  rw [rootMap_apply]
  constructor
  · intro h
    have h' := W.sub_mem h (W.smul_mem (c * δ a z) ha)
    simpa using h'
  · intro h
    exact W.add_mem h (W.smul_mem _ ha)

private theorem exists_common {A : Submodule K V} {δ : V → Dual K V} {u u' : V}
    (h1 : ∃ y ∈ A, δ u y ≠ 0) (h2 : ∃ y ∈ A, δ u' y ≠ 0) :
    ∃ w ∈ A, δ u w ≠ 0 ∧ δ u' w ≠ 0 := by
  obtain ⟨y₁, hy₁, hu₁⟩ := h1
  obtain ⟨y₂, hy₂, hu₂⟩ := h2
  by_cases a : δ u' y₁ ≠ 0
  · exact ⟨y₁, hy₁, hu₁, a⟩
  by_cases b : δ u y₂ ≠ 0
  · exact ⟨y₂, hy₂, b, hu₂⟩
  push Not at a b
  refine ⟨y₁ + y₂, A.add_mem hy₁ hy₂, ?_, ?_⟩
  · rw [map_add, b, add_zero]
    exact hu₁
  · rw [map_add, a, zero_add]
    exact hu₂

private theorem exists_on_Wp {δ : V → Dual K V} {e f : V} (hD : SympHyp δ) (P : HypPair δ e f)
    {u : V} (hu : u ∈ Wp δ e f) (hu0 : u ≠ 0) : ∃ y ∈ Wp δ e f, δ u y ≠ 0 := by
  by_contra h
  push Not at h
  apply hD.1 u hu0
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  have hx : x = qmap δ e f x + pmap δ e f x := by
    rw [pmap_apply]
    abel
  have h2 := congrArg (δ u) hx
  rw [map_add, delta_qmap_of_mem hD.2.2.1 hu x, zero_add, h _ (pmap_mem P x)] at h2
  exact h2

private theorem glue_e_apply {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (c : K) (x : V) :
    glue P β' c e x = -(c * (δ f e * δ e x)) := by
  rw [glue_apply, P.ee, pW_e P, map_zero, LinearMap.zero_apply]
  ring

private theorem glue_f_apply {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (c : K) (x : V) :
    glue P β' c f x = c * δ e f * δ f x := by
  rw [glue_apply, P.ff, pW_f P, map_zero, LinearMap.zero_apply]
  ring

private theorem prop_e {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) {c : K} (hc : c ≠ 0) (x : V) :
    δ e x = (-(c * δ f e))⁻¹ * glue P β' c e x := by
  have hne : -(c * δ f e) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hc P.fe)
  have h : -(c * (δ f e * δ e x)) = -(c * δ f e) * δ e x := by ring
  rw [glue_e_apply, h, inv_mul_cancel_left₀ hne]

private theorem prop_f {δ : V → Dual K V} {e f : V} (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) {c : K} (hc : c ≠ 0) (x : V) :
    δ f x = (c * δ e f)⁻¹ * glue P β' c f x := by
  rw [glue_f_apply, inv_mul_cancel_left₀ (mul_ne_zero hc P.ef)]

private theorem glue_prop_Wp {δ : V → Dual K V} {e f : V} (hD : SympHyp δ)
    (P : HypPair δ e f) (β' : LinearMap.BilinForm K (Wp δ e f)) (hnd : β'.Nondegenerate)
    (hiff : ∀ u v : Wp δ e f, (u : V) ≠ 0 → (β' u v = 0 ↔ δ u v = 0)) (c : K)
    {u : V} (hu : u ∈ Wp δ e f) (hu0 : u ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ x, δ u x = κ * glue P β' c u x := by
  have hφ : ∃ w, β' ⟨u, hu⟩ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (congrArg Subtype.val (hnd.1 _ h))
  obtain ⟨κ, hκ⟩ := prop_of_ker (φ := β' ⟨u, hu⟩)
    (ψ := (δ u).comp (Wp δ e f).subtype) hφ (fun w hw => (hiff ⟨u, hu⟩ w hu0).1 hw)
  have hκ0 : κ ≠ 0 := by
    obtain ⟨w, hw⟩ := hφ
    intro hκ'
    have h1 : δ u (w : V) = 0 := by
      have := hκ w
      rw [hκ', zero_mul] at this
      exact this
    exact hw ((hiff ⟨u, hu⟩ w hu0).2 h1)
  refine ⟨κ, hκ0, fun x => ?_⟩
  have hxq : x = qmap δ e f x + pmap δ e f x := by
    rw [pmap_apply]
    abel
  have hx' : δ u x = δ u (pmap δ e f x) := by
    have h := congrArg (δ u) hxq
    rw [map_add, delta_qmap_of_mem hD.2.2.1 hu x, zero_add] at h
    exact h
  have hpu : pW P u = ⟨u, hu⟩ := Subtype.ext (pmap_of_mem hu)
  obtain ⟨h1, h2⟩ := mem_Wp.1 hu
  rw [hx', glue_apply, h1, h2, hpu]
  have hk := hκ (pW P x)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hk
  show δ u ((pW P x : Wp δ e f) : V) = _
  rw [hk]
  ring

private theorem z_choice {δ : V → Dual K V} {e f : V} (hD : SympHyp δ) (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (hnd : β'.Nondegenerate)
    (hiff : ∀ u v : Wp δ e f, (u : V) ≠ 0 → (β' u v = 0 ↔ δ u v = 0))
    {u₀ : V} (hu₀ : u₀ ∈ Wp δ e f) (hu₀0 : u₀ ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ x, δ (e + u₀) x = 0 ↔ glue P β' c (e + u₀) x = 0 := by
  obtain ⟨hu₀e, hu₀f⟩ := mem_Wp.1 hu₀
  have hez : δ e (e + u₀) = 0 := by rw [map_add, P.ee, hu₀e, add_zero]
  have hze : δ (e + u₀) e = 0 := (hD.2.2.1 e (e + u₀)).1 hez
  have hzf : δ f (e + u₀) = δ f e := by rw [map_add, hu₀f, add_zero]
  have hzf' : δ (e + u₀) f ≠ 0 := fun h => P.fe (by
    rw [← hzf]
    exact (hD.2.2.1 (e + u₀) f).1 h)
  have hkey : ∀ y : Wp δ e f, δ (e + u₀) (y : V) = 0 ↔ δ u₀ (y : V) = 0 := by
    intro y
    obtain ⟨hy1, -⟩ := mem_Wp.1 y.2
    have hye : δ (y : V) e = 0 := (hD.2.2.1 e y).1 hy1
    rw [hD.2.2.1 (e + u₀) (y : V), map_add, hye, zero_add, hD.2.2.1 u₀ (y : V)]
  have hφ : ∃ w : Wp δ e f, β' ⟨u₀, hu₀⟩ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hu₀0 (congrArg Subtype.val (hnd.1 _ h))
  obtain ⟨κ₁, hκ₁⟩ := prop_of_ker (φ := β' ⟨u₀, hu₀⟩)
    (ψ := (δ (e + u₀)).comp (Wp δ e f).subtype) hφ
    (fun w hw => (hkey w).2 ((hiff ⟨u₀, hu₀⟩ w hu₀0).1 hw))
  have hκ₁0 : κ₁ ≠ 0 := by
    obtain ⟨w, hw⟩ := hφ
    intro hκ'
    have h1 : δ (e + u₀) (w : V) = 0 := by
      have := hκ₁ w
      rw [hκ', zero_mul] at this
      exact this
    exact hw ((hiff ⟨u₀, hu₀⟩ w hu₀0).2 ((hkey w).1 h1))
  obtain ⟨c, hc_def⟩ : ∃ c : K, c = -((δ e f)⁻¹ * δ (e + u₀) f) / (κ₁ * δ f e) := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    rw [hc_def]
    exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (inv_ne_zero P.ef) hzf'))
      (mul_ne_zero hκ₁0 P.fe)
  have hcK : κ₁ * c * δ f e = -((δ e f)⁻¹ * δ (e + u₀) f) := by
    have hef : δ e f ≠ 0 := P.ef
    have hfe : δ f e ≠ 0 := P.fe
    rw [hc_def]
    field_simp
  refine ⟨c, hc, fun x => ?_⟩
  have hxq : x = qmap δ e f x + pmap δ e f x := by
    rw [pmap_apply]
    abel
  have hzx := congrArg (δ (e + u₀)) hxq
  rw [map_add] at hzx
  have hqz : δ (e + u₀) (qmap δ e f x) = (δ e f)⁻¹ * δ e x * δ (e + u₀) f := by
    simp only [qmap_apply, map_add, map_smul, hze, smul_eq_mul, mul_zero, zero_add]
  have hpz : δ (e + u₀) (pmap δ e f x) = κ₁ * β' ⟨u₀, hu₀⟩ (pW P x) := by
    have hk := hκ₁ (pW P x)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hk
    exact hk
  have hpz' : pW P (e + u₀) = ⟨u₀, hu₀⟩ := by
    rw [map_add, pW_e P, zero_add]
    exact Subtype.ext (pmap_of_mem hu₀)
  have hgz : glue P β' c (e + u₀) x = c * (0 * δ f x - δ f e * δ e x) + β' ⟨u₀, hu₀⟩ (pW P x) := by
    rw [glue_apply, hez, hzf, hpz']
  have hid : δ (e + u₀) x = κ₁ * glue P β' c (e + u₀) x := by
    rw [hzx, hqz, hpz, hgz]
    linear_combination (δ e x) * hcK
  constructor
  · intro h
    rw [hid] at h
    exact (mul_eq_zero.1 h).resolve_left hκ₁0
  · intro h
    rw [hid, h, mul_zero]

private theorem words_W {δ : V → Dual K V} {e f : V} (hD : SympHyp δ) (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (hβ' : ∀ x, β' x x = 0) {c : K} (hc : c ≠ 0)
    (a b : K) (hab : a • e + b • f ≠ 0) :
    ∃ g : V →ₗ[K] V, Good δ (glue P β' c) g ∧ g e = a • e + b • f ∧
      ∀ y ∈ Wp δ e f, g y = y := by
  have hβ := glue_alt P β' hβ' c
  have hRe : ∀ t : K, Good δ (glue P β' c) (rootMap δ e t) := fun t =>
    good_of_prop hβ hD.2.1 t _ (fun x => prop_e P β' hc x) (hD.2.2.2 e t)
  have hRf : ∀ s : K, Good δ (glue P β' c) (rootMap δ f s) := fun s =>
    good_of_prop hβ hD.2.1 s _ (fun x => prop_f P β' hc x) (hD.2.2.2 f s)
  have hfixe : ∀ t : K, ∀ y ∈ Wp δ e f, rootMap δ e t y = y := fun t y hy => by
    rw [rootMap_apply, (mem_Wp.1 hy).1, mul_zero, zero_smul, add_zero]
  have hfixf : ∀ s : K, ∀ y ∈ Wp δ e f, rootMap δ f s y = y := fun s y hy => by
    rw [rootMap_apply, (mem_Wp.1 hy).2, mul_zero, zero_smul, add_zero]
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      intro ha
      apply hab
      rw [ha, hb, zero_smul, zero_smul, add_zero]
    obtain ⟨s₁, hs₁⟩ : ∃ s : K, s * δ f e = 1 := ⟨(δ f e)⁻¹, inv_mul_cancel₀ P.fe⟩
    obtain ⟨t, ht⟩ : ∃ t : K, t * δ e f = a - 1 :=
      ⟨(a - 1) * (δ e f)⁻¹, by rw [mul_assoc, inv_mul_cancel₀ P.ef, mul_one]⟩
    obtain ⟨s₂, hs₂⟩ : ∃ s : K, s * (a * δ f e) = -1 :=
      ⟨-(a * δ f e)⁻¹, by rw [neg_mul, inv_mul_cancel₀ (mul_ne_zero ha P.fe)]⟩
    have v1 : rootMap δ f s₁ e = e + f := by
      rw [rootMap_apply, hs₁, one_smul]
    have v2 : rootMap δ e t (e + f) = a • e + f := by
      rw [rootMap_apply, map_add, P.ee, zero_add, ht]
      module
    have v3 : rootMap δ f s₂ (a • e + f) = a • e := by
      rw [rootMap_apply, map_add, map_smul, P.ff, add_zero, smul_eq_mul, hs₂]
      module
    refine ⟨rootMap δ f s₂ ∘ₗ (rootMap δ e t ∘ₗ rootMap δ f s₁),
      good_comp (hRf s₂) (good_comp (hRe t) (hRf s₁)), ?_, ?_⟩
    · show rootMap δ f s₂ (rootMap δ e t (rootMap δ f s₁ e)) = a • e + b • f
      rw [v1, v2, v3, hb, zero_smul, add_zero]
    · intro y hy
      show rootMap δ f s₂ (rootMap δ e t (rootMap δ f s₁ y)) = y
      rw [hfixf s₁ y hy, hfixe t y hy, hfixf s₂ y hy]
  · obtain ⟨s, hs⟩ : ∃ s : K, s * δ f e = b :=
      ⟨b * (δ f e)⁻¹, by rw [mul_assoc, inv_mul_cancel₀ P.fe, mul_one]⟩
    obtain ⟨t, ht⟩ : ∃ t : K, t * (b * δ e f) = a - 1 :=
      ⟨(a - 1) * (b * δ e f)⁻¹, by
        rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero hb P.ef), mul_one]⟩
    have v1 : rootMap δ f s e = e + b • f := by
      rw [rootMap_apply, hs]
    have v2 : rootMap δ e t (e + b • f) = a • e + b • f := by
      rw [rootMap_apply, map_add, map_smul, P.ee, zero_add, smul_eq_mul, ht]
      module
    refine ⟨rootMap δ e t ∘ₗ rootMap δ f s, good_comp (hRe t) (hRf s), ?_, ?_⟩
    · show rootMap δ e t (rootMap δ f s e) = a • e + b • f
      rw [v1, v2]
    · intro y hy
      show rootMap δ e t (rootMap δ f s y) = y
      rw [hfixf s y hy, hfixe t y hy]

private theorem words_Wp {δ : V → Dual K V} {e f : V} (hD : SympHyp δ) (P : HypPair δ e f)
    {β : LinearMap.BilinForm K V} (hβ : ∀ x, β x x = 0)
    (hW : ∀ a ∈ Wp δ e f, a ≠ 0 → ∃ κ : K, ∀ x, δ a x = κ * β a x)
    {u u' : V} (hu : u ∈ Wp δ e f) (hu' : u' ∈ Wp δ e f) (hu0 : u ≠ 0) (hu'0 : u' ≠ 0) :
    ∃ g : V →ₗ[K] V, Good δ β g ∧ g u = u' ∧ g e = e ∧ g f = f := by
  have hfixef : ∀ a ∈ Wp δ e f, δ a e = 0 ∧ δ a f = 0 := fun a ha =>
    ⟨(hD.2.2.1 e a).1 (mem_Wp.1 ha).1, (hD.2.2.1 f a).1 (mem_Wp.1 ha).2⟩
  have step : ∀ x y : V, y - x ∈ Wp δ e f → δ x y ≠ 0 →
      ∃ g : V →ₗ[K] V, Good δ β g ∧ g x = y ∧ ∀ z, δ (y - x) z = 0 → g z = z := by
    intro x y hyx hxy
    have hne : y - x ≠ 0 := sub_ne_zero.2 (fun h => hxy (by rw [h]; exact hD.2.1 x))
    obtain ⟨κ, hκ⟩ := hW (y - x) hyx hne
    have hax : δ (y - x) x ≠ 0 := fun h => hxy (by
      have h' := (hD.2.2.1 x (y - x)).2 h
      rw [map_sub, hD.2.1 x, sub_zero] at h'
      exact h')
    refine ⟨rootMap δ (y - x) (δ (y - x) x)⁻¹,
      good_of_prop hβ hD.2.1 ((δ (y - x) x)⁻¹) κ hκ (hD.2.2.2 _ _), ?_, ?_⟩
    · rw [rootMap_apply, inv_mul_cancel₀ hax, one_smul]
      abel
    · intro z hz
      rw [rootMap_apply, hz, mul_zero, zero_smul, add_zero]
  by_cases hA : δ u u' ≠ 0
  · obtain ⟨g, hg, hgu, hgfix⟩ := step u u' (Submodule.sub_mem _ hu' hu) hA
    exact ⟨g, hg, hgu, hgfix e (hfixef _ (Submodule.sub_mem _ hu' hu)).1,
      hgfix f (hfixef _ (Submodule.sub_mem _ hu' hu)).2⟩
  · obtain ⟨w, hw, hwu, hwu'⟩ := exists_common (A := Wp δ e f)
      (exists_on_Wp hD P hu hu0) (exists_on_Wp hD P hu' hu'0)
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ := step u w (Submodule.sub_mem _ hw hu) hwu
    obtain ⟨g₂, hg₂, hg₂w, hg₂fix⟩ := step w u' (Submodule.sub_mem _ hu' hw)
      (fun h => hwu' ((hD.2.2.1 w u').1 h))
    refine ⟨g₂ ∘ₗ g₁, good_comp hg₂ hg₁, ?_, ?_, ?_⟩
    · show g₂ (g₁ u) = u'
      rw [hg₁u, hg₂w]
    · show g₂ (g₁ e) = e
      rw [hg₁fix e (hfixef _ (Submodule.sub_mem _ hw hu)).1,
        hg₂fix e (hfixef _ (Submodule.sub_mem _ hu' hw)).1]
    · show g₂ (g₁ f) = f
      rw [hg₁fix f (hfixef _ (Submodule.sub_mem _ hw hu)).2,
        hg₂fix f (hfixef _ (Submodule.sub_mem _ hu' hw)).2]

private theorem build {δ : V → Dual K V} {e f : V} (hD : SympHyp δ) (P : HypPair δ e f)
    (β' : LinearMap.BilinForm K (Wp δ e f)) (hnd : β'.Nondegenerate) (hβ' : ∀ x, β' x x = 0)
    (hiff : ∀ u v : Wp δ e f, (u : V) ≠ 0 → (β' u v = 0 ↔ δ u v = 0)) {c : K} (hc : c ≠ 0)
    (hz : (∃ u₀ ∈ Wp δ e f, u₀ ≠ 0 ∧ ∀ x, δ (e + u₀) x = 0 ↔ glue P β' c (e + u₀) x = 0) ∨
      ∀ u ∈ Wp δ e f, u = 0) :
    Concl δ (glue P β' c) := by
  have hβ := glue_alt P β' hβ' c
  have hW : ∀ a ∈ Wp δ e f, a ≠ 0 → ∃ κ : K, ∀ x, δ a x = κ * glue P β' c a x := by
    intro a ha ha0
    obtain ⟨κ, -, hκ⟩ := glue_prop_Wp hD P β' hnd hiff c ha ha0
    exact ⟨κ, hκ⟩
  have hKe : ∀ x, δ e x = 0 ↔ glue P β' c e x = 0 :=
    kr_of_prop (inv_ne_zero (neg_ne_zero.2 (mul_ne_zero hc P.fe))) (fun x => prop_e P β' hc x)
  have hKw : ∀ a b : K, a • e + b • f ≠ 0 → ∀ y, δ (a • e + b • f) y = 0 ↔
      glue P β' c (a • e + b • f) y = 0 := by
    intro a b hab y
    obtain ⟨g, hg, hge, -⟩ := words_W hD P β' hβ' hc a b hab
    have h := transport hg hKe y
    rw [hge] at h
    exact h
  have hKall : ∀ v, v ≠ 0 → ∀ x, δ v x = 0 ↔ glue P β' c v x = 0 := by
    intro v hv x
    have hdec : v = qmap δ e f v + pmap δ e f v := by
      rw [pmap_apply]
      abel
    by_cases hu' : pmap δ e f v = 0
    · have hv' : v = qmap δ e f v := by
        have h := hdec
        rw [hu', add_zero] at h
        exact h
      obtain ⟨a, b, hab⟩ : ∃ a b : K, qmap δ e f v = a • e + b • f :=
        ⟨_, _, qmap_apply δ e f v⟩
      have hne : a • e + b • f ≠ 0 := by
        rw [← hab, ← hv']
        exact hv
      have hvab : v = a • e + b • f := hv'.trans hab
      rw [hvab]
      exact hKw a b hne x
    · by_cases hw : qmap δ e f v = 0
      · have hv' : v = pmap δ e f v := by
          have h := hdec
          rw [hw, zero_add] at h
          exact h
        have hvW : v ∈ Wp δ e f := by
          have h := pmap_mem P v
          rw [← hv'] at h
          exact h
        obtain ⟨κ, hκ0, hκ⟩ := glue_prop_Wp hD P β' hnd hiff c hvW hv
        exact kr_of_prop hκ0 hκ x
      · obtain ⟨u₀, hu₀, hu₀0, hKz⟩ : ∃ u₀ ∈ Wp δ e f, u₀ ≠ 0 ∧
            ∀ x, δ (e + u₀) x = 0 ↔ glue P β' c (e + u₀) x = 0 := by
          rcases hz with h | h
          · exact h
          · exact absurd (h _ (pmap_mem P v)) hu'
        obtain ⟨a, b, hab⟩ : ∃ a b : K, qmap δ e f v = a • e + b • f :=
          ⟨_, _, qmap_apply δ e f v⟩
        have hwne : a • e + b • f ≠ 0 := by
          rw [← hab]
          exact hw
        obtain ⟨g₁, hg₁, hg₁e, hg₁fix⟩ := words_W hD P β' hβ' hc a b hwne
        obtain ⟨g₂, hg₂, hg₂u, hg₂e, hg₂f⟩ :=
          words_Wp hD P hβ hW hu₀ (pmap_mem P v) hu₀0 hu'
        have hgv : (g₂ ∘ₗ g₁) (e + u₀) = v := by
          show g₂ (g₁ (e + u₀)) = v
          rw [map_add, hg₁e, hg₁fix u₀ hu₀, map_add, map_add, map_smul, map_smul, hg₂e, hg₂f,
            hg₂u, ← hab]
          exact hdec.symm
        have h := transport (good_comp hg₂ hg₁) hKz x
        rw [hgv] at h
        exact h
  exact ⟨glue_nondeg P β' hnd hβ' hc, hβ, fun v w hv => (hKall v hv w).symm⟩

private def restrictD (δ : V → Dual K V) (W : Submodule K V) : W → Dual K W :=
  fun u => (δ (u : V)).comp W.subtype

private theorem restrictD_apply {δ : V → Dual K V} {W : Submodule K V} (u v : W) :
    restrictD δ W u v = δ (u : V) (v : V) :=
  rfl

private theorem restrict_symp {δ : V → Dual K V} {e f : V} (hD : SympHyp δ)
    (P : HypPair δ e f) : SympHyp (restrictD δ (Wp δ e f)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu h
    obtain ⟨y, hy, hne⟩ := exists_on_Wp hD P u.2 (fun h0 => hu (Subtype.ext h0))
    apply hne
    have h2 := LinearMap.congr_fun h ⟨y, hy⟩
    simpa [restrictD] using h2
  · intro u
    exact hD.2.1 u
  · intro u v
    exact hD.2.2.1 u v
  · intro a c x y
    have ha : (a : V) ∈ Wp δ e f := a.2
    have hcoe : ∀ z : Wp δ e f, ((rootMap (restrictD δ (Wp δ e f)) a c z : Wp δ e f) : V) =
        rootMap δ (a : V) c (z : V) := by
      intro z
      simp only [rootMap_apply, restrictD_apply, Submodule.coe_add, Submodule.coe_smul]
    rw [restrictD_apply, hcoe x]
    constructor
    · intro h
      obtain ⟨z, hz, hRz⟩ := (hD.2.2.2 (a : V) c (x : V) (y : V)).1 h
      have hzW : z ∈ Wp δ e f := (mem_rootMap_iff ha c z).1 (by rw [hRz]; exact y.2)
      refine ⟨⟨z, hzW⟩, hz, ?_⟩
      apply Subtype.ext
      rw [hcoe ⟨z, hzW⟩]
      exact hRz
    · rintro ⟨z, hz, hRz⟩
      refine (hD.2.2.2 (a : V) c (x : V) (y : V)).2 ⟨(z : V), hz, ?_⟩
      rw [← hcoe z, hRz]

private theorem key : ∀ (n : ℕ) (X : Type u) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
    finrank K X = n → ∀ δ : X → Dual K X, SympHyp δ →
      ∃ β : LinearMap.BilinForm K X, Concl δ β := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn δ hD
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    · haveI : Subsingleton X := Module.finrank_zero_iff.1 hn
      exact ⟨0, ⟨fun x _ => Subsingleton.elim _ _, fun y _ => Subsingleton.elim _ _⟩,
        fun x => by simp, fun v w hv => absurd (Subsingleton.elim v 0) hv⟩
    · exfalso
      obtain ⟨e, he, hspan⟩ := finrank_eq_one_iff'.1 hn
      obtain ⟨f, hf⟩ : ∃ f, δ e f ≠ 0 := by
        by_contra h
        push Not at h
        exact hD.1 e he (LinearMap.ext fun x => by simpa using h x)
      obtain ⟨c, rfl⟩ := hspan f
      exact hf (by rw [map_smul, hD.2.1 e, smul_zero])
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hpos : 0 < finrank K X := by
      rw [hn]
      omega
    haveI : Nontrivial X := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨e, he⟩ := exists_ne (0 : X)
    obtain ⟨f, hf⟩ : ∃ f, δ e f ≠ 0 := by
      by_contra h
      push Not at h
      exact hD.1 e he (LinearMap.ext fun x => by simpa using h x)
    let P : HypPair δ e f := ⟨hD.2.1 e, hD.2.1 f, hf, fun h => hf ((hD.2.2.1 e f).2 h)⟩
    have hWne : Wp δ e f ≠ ⊤ := by
      intro h
      have he' : e ∈ Wp δ e f := by
        rw [h]
        exact Submodule.mem_top
      exact P.fe (mem_Wp.1 he').2
    have hlt : finrank K (Wp δ e f) < m + 2 := by
      have := Submodule.finrank_lt hWne
      omega
    obtain ⟨β', hnd, hβ'alt, hiff⟩ :=
      ih _ hlt (Wp δ e f) rfl (restrictD δ (Wp δ e f)) (restrict_symp hD P)
    have hiff' : ∀ u v : Wp δ e f, (u : X) ≠ 0 → (β' u v = 0 ↔ δ u v = 0) := fun u v hu =>
      hiff u v (fun h => hu (congrArg Subtype.val h))
    by_cases hW : ∃ u ∈ Wp δ e f, u ≠ 0
    · obtain ⟨u₀, hu₀, hu₀0⟩ := hW
      obtain ⟨c, hc, hKz⟩ := z_choice hD P β' hnd hiff' hu₀ hu₀0
      exact ⟨glue P β' c, build hD P β' hnd hβ'alt hiff' hc (Or.inl ⟨u₀, hu₀, hu₀0, hKz⟩)⟩
    · push Not at hW
      exact ⟨glue P β' 1, build hD P β' hnd hβ'alt hiff' one_ne_zero (Or.inr hW)⟩

end Basic

section Main

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_alt_form_of_sympData (δ : V → Module.Dual K V) (hδ0 : ∀ v, v ≠ 0 → δ v ≠ 0)
    (hδv : ∀ v, δ v v = 0)
    (hsymm : ∀ v w, δ v w = 0 ↔ δ w v = 0)
    (Y : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hY : Y = Subgroup.closure {g : LinearMap.GeneralLinearGroup K V |
      ∃ (v : V) (c : K), (g : V →ₗ[K] V) = 1 + c • (δ v).smulRight v})
    (hinv : ∀ y ∈ Y, ∀ v, LinearMap.ker (δ ((y : V →ₗ[K] V) v)) =
      (LinearMap.ker (δ v)).map (y : V →ₗ[K] V)) :
    ∃ β : LinearMap.BilinForm K V, β.Nondegenerate ∧ (∀ x, β x x = 0) ∧
      ∀ v w, v ≠ 0 → (β v w = 0 ↔ δ v w = 0) := by
  have hP : ∀ (a : V) (c : K), Pres δ (rootMap δ a c) := by
    intro a c
    have hNN : ∀ x, (δ a).smulRight a ((δ a).smulRight a x) = 0 := fun x => by
      simp [hδv a]
    have hL : (1 + c • (δ a).smulRight a) * (1 - c • (δ a).smulRight a) = 1 := by
      ext x
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
        Module.End.one_apply, LinearMap.smul_apply, map_sub, map_add, map_smul, hNN, smul_zero,
        add_zero, sub_zero]
      module
    have hR : (1 - c • (δ a).smulRight a) * (1 + c • (δ a).smulRight a) = 1 := by
      ext x
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
        Module.End.one_apply, LinearMap.smul_apply, map_sub, map_add, map_smul, hNN, smul_zero,
        add_zero, sub_zero]
      module
    let g : LinearMap.GeneralLinearGroup K V :=
      ⟨1 + c • (δ a).smulRight a, 1 - c • (δ a).smulRight a, hL, hR⟩
    have hg : g ∈ Y := by
      rw [hY]
      exact Subgroup.subset_closure ⟨a, c, rfl⟩
    intro x y
    have h := hinv g hg x
    have hm : y ∈ LinearMap.ker (δ ((g : V →ₗ[K] V) x)) ↔
        y ∈ (LinearMap.ker (δ x)).map (g : V →ₗ[K] V) := by
      rw [h]
    simp only [LinearMap.mem_ker, Submodule.mem_map] at hm
    exact hm
  obtain ⟨β, hβ⟩ := key (Module.finrank K V) V rfl δ ⟨hδ0, hδv, hsymm, hP⟩
  exact ⟨β, hβ.1, hβ.2.1, hβ.2.2⟩

end Main

end CFSG.ClassicalGroups.McLaughlin
