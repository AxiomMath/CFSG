module

public import CFSG.LargeExtraspecial.S2OrthB1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_zero_right eichler_conj
  eichler_add_smul_self)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}

structure IsAutOn (F : Submodule (ZMod 2) V) (α : omegaGroup q hq → omegaGroup q hq) :
    Prop where
  mem : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F
  map_mul : ∀ g h : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α (g * h) = α g * α h
  inj : ∀ g h : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α g = α h → g = h
  surj : ∀ h : omegaGroup q hq, (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    ∃ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F ∧ α g = h

@[expose] def MapsRad (F : Submodule (ZMod 2) V) (α : omegaGroup q hq → omegaGroup q hq)
    (a b : V) : Prop :=
  ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    ((g : V ≃ₗ[ZMod 2] V) ∈ radFix q F a ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ radFix q F b)

theorem coe_mul_mem_fixGroup {F : Submodule (ZMod 2) V} {g h : omegaGroup q hq}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) (hh : (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    ((g * h : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) ∈ fixGroup F :=
  mul_mem hg hh

theorem coe_inv_mem_fixGroup {F : Submodule (ZMod 2) V} {g : omegaGroup q hq}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    ((g⁻¹ : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) ∈ fixGroup F :=
  inv_mem hg

namespace IsAutOn

variable {F : Submodule (ZMod 2) V} {α : omegaGroup q hq → omegaGroup q hq}

theorem map_one (hα : IsAutOn F α) : α 1 = 1 := by
  have h := hα.map_mul 1 1 (one_mem (fixGroup F)) (one_mem (fixGroup F))
  rw [mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem map_inv (hα : IsAutOn F α) {g : omegaGroup q hq}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) : α g⁻¹ = (α g)⁻¹ := by
  have h := hα.map_mul g g⁻¹ hg (coe_inv_mem_fixGroup hg)
  rw [mul_inv_cancel, hα.map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem map_conj (hα : IsAutOn F α) {g t : omegaGroup q hq}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) (ht : (t : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    α (g⁻¹ * t * g) = (α g)⁻¹ * α t * α g := by
  rw [hα.map_mul _ _ (coe_mul_mem_fixGroup (coe_inv_mem_fixGroup hg) ht) hg,
    hα.map_mul _ _ (coe_inv_mem_fixGroup hg) ht, hα.map_inv hg]

theorem conj (hα : IsAutOn F α) {x : omegaGroup q hq} (hx : (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    IsAutOn F (fun g => x * α g * x⁻¹) where
  mem g hg := coe_mul_mem_fixGroup (coe_mul_mem_fixGroup hx (hα.mem g hg))
    (coe_inv_mem_fixGroup hx)
  map_mul g h hg hh := by
    rw [hα.map_mul g h hg hh]
    group
  inj g h hg hh e := hα.inj g h hg hh (by simpa using e)
  surj h hh := by
    obtain ⟨g, hg, hgh⟩ := hα.surj (x⁻¹ * h * x)
      (coe_mul_mem_fixGroup (coe_mul_mem_fixGroup (coe_inv_mem_fixGroup hx) hh) hx)
    exact ⟨g, hg, by rw [hgh]; group⟩

theorem restrict (hα : IsAutOn F α) {K : Submodule (ZMod 2) V} (hKF : fixGroup K ≤ fixGroup F)
    (hK : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K)) :
    IsAutOn K α where
  mem g hg := (hK g (hKF hg)).mp hg
  map_mul g h hg hh := hα.map_mul g h (hKF hg) (hKF hh)
  inj g h hg hh := hα.inj g h (hKF hg) (hKF hh)
  surj h hh := by
    obtain ⟨g, hg, rfl⟩ := hα.surj h (hKF hh)
    exact ⟨g, (hK g hg).mpr hh, rfl⟩

theorem inner_of_conj {x y : omegaGroup q hq}
    (h : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → x * α g * x⁻¹ = y * g * y⁻¹)
    (g : omegaGroup q hq) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    α g = (x⁻¹ * y) * g * (x⁻¹ * y)⁻¹ := by
  calc α g = x⁻¹ * (x * α g * x⁻¹) * x := by group
    _ = (x⁻¹ * y) * g * (x⁻¹ * y)⁻¹ := by rw [h g hg]; group

end IsAutOn

theorem MapsRad.conj {F : Submodule (ZMod 2) V} {α : omegaGroup q hq → omegaGroup q hq}
    {a b : V} (h : MapsRad F α a b) {x : omegaGroup q hq}
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) (hb0 : b ≠ 0) (hb : q b = 0)
    (hbF : b ∈ perp q F) :
    MapsRad F (fun g => x * α g * x⁻¹) a ((x : V ≃ₗ[ZMod 2] V) b) := by
  intro g hg
  have hxO : (x : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp x.2).1
  rw [h g hg, map_conj_radFix hq hb0 hb hbF hxO hx]
  change _ ↔ (x : V ≃ₗ[ZMod 2] V)⁻¹ * ((x : V ≃ₗ[ZMod 2] V) * (α g : V ≃ₗ[ZMod 2] V) *
    (x : V ≃ₗ[ZMod 2] V)⁻¹) * (x : V ≃ₗ[ZMod 2] V) ∈ _
  rw [show (x : V ≃ₗ[ZMod 2] V)⁻¹ * ((x : V ≃ₗ[ZMod 2] V) * (α g : V ≃ₗ[ZMod 2] V) *
    (x : V ≃ₗ[ZMod 2] V)⁻¹) * (x : V ≃ₗ[ZMod 2] V) = (α g : V ≃ₗ[ZMod 2] V) by group]

theorem eq_of_forall_mem_radFix_iff {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥)
    (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {a b : V} (haF : a ∈ perp q F) (hbF : b ∈ perp q F)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : q a = 0) (hb : q b = 0)
    (h : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ radFix q F a ↔ (g : V ≃ₗ[ZMod 2] V) ∈ radFix q F b)) :
    a = b := by
  refine eq_of_radFix_eq hq hF h4 haF hbF ha0 hb0 ha ?_
  ext t
  constructor
  · intro ht
    have htΩ := radFix_le_omegaFix hq ha0 ha ht
    exact (h ⟨t, htΩ.1⟩ htΩ.2).mp ht
  · intro ht
    have htΩ := radFix_le_omegaFix hq hb0 hb ht
    exact (h ⟨t, htΩ.1⟩ htΩ.2).mpr ht

namespace IsAutOn

variable {F : Submodule (ZMod 2) V} {α : omegaGroup q hq → omegaGroup q hq}

theorem mapsRad_apply (hα : IsAutOn F α) {a : V} (ha0 : a ≠ 0) (ha : q a = 0)
    (haF : a ∈ perp q F) (hαa : MapsRad F α a a) {g : omegaGroup q hq}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    MapsRad F α ((g : V ≃ₗ[ZMod 2] V) a) ((α g : V ≃ₗ[ZMod 2] V) a) := by
  intro t ht
  have hgO : (g : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp g.2).1
  have hαgO : (α g : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp (α g).2).1
  rw [map_conj_radFix hq ha0 ha haF hgO hg, map_conj_radFix hq ha0 ha haF hαgO (hα.mem g hg)]
  have h := hαa (g⁻¹ * t * g) (coe_mul_mem_fixGroup (coe_mul_mem_fixGroup
    (coe_inv_mem_fixGroup hg) ht) hg)
  rw [hα.map_conj hg ht] at h
  exact h

theorem eq_of_mapsRad (hF : F ⊓ perp q F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (perp q F))
    {a a' b : V} (haF : a ∈ perp q F) (ha'F : a' ∈ perp q F) (ha0 : a ≠ 0) (ha'0 : a' ≠ 0)
    (ha : q a = 0) (ha' : q a' = 0) (h : MapsRad F α a b) (h' : MapsRad F α a' b) : a = a' :=
  eq_of_forall_mem_radFix_iff (hq := hq) hF h4 haF ha'F ha0 ha'0 ha ha' fun g hg =>
    (h g hg).trans (h' g hg).symm

theorem eq_of_mapsRad' (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥)
    (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {a b b' : V} (hbF : b ∈ perp q F)
    (hb'F : b' ∈ perp q F) (hb0 : b ≠ 0) (hb'0 : b' ≠ 0) (hb : q b = 0) (hb' : q b' = 0)
    (h : MapsRad F α a b) (h' : MapsRad F α a b') : b = b' := by
  refine eq_of_forall_mem_radFix_iff (hq := hq) hF h4 hbF hb'F hb0 hb'0 hb hb' fun s hs => ?_
  obtain ⟨t, ht, rfl⟩ := hα.surj s hs
  exact (h t ht).symm.trans (h' t ht)

theorem mapsRad_inf_eq_bot_iff (hα : IsAutOn F α) {a b a' b' : V} (ha0 : a ≠ 0) (ha : q a = 0)
    (ha'0 : a' ≠ 0) (ha' : q a' = 0) (h1 : MapsRad F α a a') (h2 : MapsRad F α b b') :
    radFix q F a ⊓ radFix q F b = ⊥ ↔ radFix q F a' ⊓ radFix q F b' = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro s ⟨hs, hs'⟩
    have hsΩ := radFix_le_omegaFix hq ha'0 ha' hs
    obtain ⟨t, ht, hts⟩ := hα.surj ⟨s, hsΩ.1⟩ hsΩ.2
    have hta : (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F a := (h1 t ht).mpr (by rw [hts]; exact hs)
    have htb : (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F b := (h2 t ht).mpr (by rw [hts]; exact hs')
    have ht1 : t = 1 := Subtype.ext (by
      have := (show (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F a ⊓ radFix q F b from ⟨hta, htb⟩)
      rw [h, Subgroup.mem_bot] at this
      exact this)
    rw [ht1, hα.map_one] at hts
    rw [Subgroup.mem_bot]
    exact (congrArg Subtype.val hts).symm
  · intro h
    rw [eq_bot_iff]
    rintro t ⟨ht, ht'⟩
    have htΩ := radFix_le_omegaFix hq ha0 ha ht
    have hs := (show ((α ⟨t, htΩ.1⟩ : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) ∈
      radFix q F a' ⊓ radFix q F b' from ⟨(h1 _ htΩ.2).mp ht, (h2 _ htΩ.2).mp ht'⟩)
    rw [h, Subgroup.mem_bot] at hs
    have : α ⟨t, htΩ.1⟩ = α 1 := by rw [hα.map_one]; exact Subtype.ext hs
    have := hα.inj _ _ htΩ.2 (one_mem _) this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this

end IsAutOn

namespace IsAutOn

variable {F : Submodule (ZMod 2) V} {α : omegaGroup q hq → omegaGroup q hq}

theorem mapsRad_polar_eq_one (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥)
    (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {a b a' b' : V} (haF : a ∈ perp q F)
    (hbF : b ∈ perp q F) (ha'F : a' ∈ perp q F) (hb'F : b' ∈ perp q F) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (ha'0 : a' ≠ 0) (hb'0 : b' ≠ 0) (ha : q a = 0) (hb : q b = 0) (ha' : q a' = 0)
    (hb' : q b' = 0) (hab : polar q a b = 1) (h1 : MapsRad F α a a') (h2 : MapsRad F α b b') :
    polar q a' b' = 1 := by
  have hne : a ≠ b := by
    rintro rfl
    rw [polar_self_eq_zero] at hab
    exact zero_ne_one hab
  have hne' : a' ≠ b' := by
    rintro rfl
    exact hne (eq_of_mapsRad hF h4 haF hbF ha0 hb0 ha hb h1 h2)
  refine (radFix_inf_eq_bot_iff hq ha'F hb'F ha'0 hb'0 hne' ha' hb').mp ?_
  exact (hα.mapsRad_inf_eq_bot_iff ha0 ha ha'0 ha' h1 h2).mp
    ((radFix_inf_eq_bot_iff hq haF hbF ha0 hb0 hne ha hb).mpr hab)

theorem mapsRad_polar_eq_zero (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥)
    (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {a b a' b' : V} (haF : a ∈ perp q F)
    (hbF : b ∈ perp q F) (ha'F : a' ∈ perp q F) (hb'F : b' ∈ perp q F) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (ha'0 : a' ≠ 0) (hb'0 : b' ≠ 0) (ha : q a = 0) (hb : q b = 0) (ha' : q a' = 0)
    (hb' : q b' = 0) (hne : a ≠ b) (hab : polar q a b = 0) (h1 : MapsRad F α a a')
    (h2 : MapsRad F α b b') : a' ≠ b' ∧ polar q a' b' = 0 := by
  have hne' : a' ≠ b' := by
    rintro rfl
    exact hne (eq_of_mapsRad hF h4 haF hbF ha0 hb0 ha hb h1 h2)
  refine ⟨hne', (zmod2_eq_zero_or_eq_one _).resolve_right fun h => ?_⟩
  have := (hα.mapsRad_inf_eq_bot_iff ha0 ha ha'0 ha' h1 h2).mpr
    ((radFix_inf_eq_bot_iff hq ha'F hb'F ha'0 hb'0 hne' ha' hb').mpr h)
  rw [(radFix_inf_eq_bot_iff hq haF hbF ha0 hb0 hne ha hb)] at this
  rw [hab] at this
  exact zero_ne_one this

theorem exists_mapsRad_conj (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥)
    (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {p p₁ : V} (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1) (hαp : MapsRad F α p p) :
    ∃ E : omegaGroup q hq, (E : V ≃ₗ[ZMod 2] V) ∈ radFix q F p ∧
      MapsRad F (fun g => E * α g * E⁻¹) p p ∧ MapsRad F (fun g => E * α g * E⁻¹) p₁ p₁ := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  obtain ⟨g, hg, hgp⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hpF hp₁F hp0 hp₁0 hp hp₁
  have hgΩ := radGen_le_omegaFix hq F hg
  set g' : omegaGroup q hq := ⟨g, hgΩ.1⟩
  have hg'F : (g' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hgΩ.2
  have h1 := hα.mapsRad_apply hp0 hp hpF hαp hg'F
  change MapsRad F α (g p) _ at h1
  rw [hgp] at h1
  set b := (α g' : V ≃ₗ[ZMod 2] V) p with hb
  have hαgO : (α g' : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp (α g').2).1
  have hbF : b ∈ perp q F := apply_mem_perp hαgO (hα.mem g' hg'F) hpF
  have hbq : q b = 0 := by rw [hb, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hαgO, hp]
  have hb0 : b ≠ 0 := fun h => hp0 ((α g' : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h)
  have hpb : polar q p b = 1 := hα.mapsRad_polar_eq_one hF h4 hpF hp₁F hpF hbF hp0 hp₁0 hp0 hb0
    hp hp₁ hp hbq hpp₁ hαp h1
  obtain ⟨E, hE, hEb⟩ := exists_mem_radFix_apply_eq hq hp0 hp hpF hbF hp₁F hbq hp₁ hpb hpp₁
  have hEΩ := radFix_le_omegaFix hq hp0 hp hE
  refine ⟨⟨E, hEΩ.1⟩, hE, ?_, ?_⟩
  · have := hαp.conj (x := ⟨E, hEΩ.1⟩) hEΩ.2 hp0 hp hpF
    rwa [show E p = p from hE.1.2.1] at this
  · have := h1.conj (x := ⟨E, hEΩ.1⟩) hEΩ.2 hb0 hbq hbF
    rwa [show E b = p₁ from hEb] at this

theorem eq_self_of_forall_radFix (hα : IsAutOn F α) (hF : F ⊓ perp q F = ⊥) {m : ℕ}
    (hm : 2 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m) {p p₁ : V} (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1)
    (h : ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p → α t = t)
    (h₁ : ∀ t : omegaGroup q hq, (t : V ≃ₗ[ZMod 2] V) ∈ radFix q F p₁ → α t = t)
    (g : omegaGroup q hq) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) : α g = g := by
  have hcl := omegaFix_eq_closure_radFix hq hF hm hdim hpF hp₁F hp0 hp hp₁ hpp₁
  have hle : Subgroup.closure ((radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ∪ radFix q F p₁) ≤
      omegaFix q hq F := hcl.symm.le
  have key : ∀ x ∈ Subgroup.closure ((radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ∪ radFix q F p₁),
      ∀ hx : x ∈ omegaGroup q hq, α ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hxΩ
      rcases hx with hx | hx
      · exact h ⟨x, hxΩ⟩ hx
      · exact h₁ ⟨x, hxΩ⟩ hx
    | one =>
      intro _
      exact hα.map_one
    | mul x y hx' hy' ihx ihy =>
      intro _
      have hxΩ := hle hx'
      have hyΩ := hle hy'
      have e : (⟨x * y, mul_mem hxΩ.1 hyΩ.1⟩ : omegaGroup q hq) =
          ⟨x, hxΩ.1⟩ * ⟨y, hyΩ.1⟩ := rfl
      rw [e, hα.map_mul _ _ hxΩ.2 hyΩ.2, ihx hxΩ.1, ihy hyΩ.1]
    | inv x hx' ihx =>
      intro _
      have hxΩ := hle hx'
      have e : (⟨x⁻¹, inv_mem hxΩ.1⟩ : omegaGroup q hq) = (⟨x, hxΩ.1⟩)⁻¹ := rfl
      rw [e, hα.map_inv hxΩ.2, ihx hxΩ.1]
  have hmem : (g : V ≃ₗ[ZMod 2] V) ∈
      Subgroup.closure ((radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ∪ radFix q F p₁) := by
    rw [← hcl]
    exact ⟨g.2, hg⟩
  exact key g hmem g.2

end IsAutOn

theorem exists_eq_eichler_perp (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p p₁ : V} (hpF : p ∈ perp q F)
    (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ radFix q F p) :
    ∃ u ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}), t = eichler q p u := by
  obtain ⟨u, huF, hpu, rfl⟩ := (mem_radFix_iff hq hp0 hp hpF).mp ht
  refine ⟨u + polar q u p₁ • p, ?_, (eichler_add_smul_self hp u _).symm⟩
  rw [mem_perp_sup_span_pair]
  refine ⟨Submodule.add_mem _ huF (Submodule.smul_mem _ _ hpF), ?_, ?_⟩
  · rw [polar_add_right, polar_smul_right, polar_self_eq_zero, hpu, smul_zero, add_zero]
  · rw [polar_add_right, polar_smul_right, polar_comm q p₁ p, hpp₁, smul_eq_mul, mul_one,
      polar_comm q p₁ u, zmod2_add_self]

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_of_eichler_eq {F : Submodule (ZMod 2) V} {p p₁ u u' : V} (hp : q p = 0)
    (hpp₁ : polar q p p₁ = 1) (hu : u ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}))
    (hu' : u' ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}))
    (h : eichler q p u = eichler q p u') : u = u' := by
  obtain ⟨-, hpu, hp₁u⟩ := mem_perp_sup_span_pair.mp hu
  obtain ⟨-, hpu', hp₁u'⟩ := mem_perp_sup_span_pair.mp hu'
  have e := congrArg (fun g : V ≃ₗ[ZMod 2] V => g p₁) h
  rw [eichler_apply_of_polar_eq_one hp hpu hpp₁, eichler_apply_of_polar_eq_one hp hpu' hpp₁,
    hp₁u, hp₁u', zero_add, zero_add, add_assoc, add_assoc] at e
  have e' := add_left_cancel e
  have hc := congrArg (fun x => polar q x p₁) e'
  simp only [polar_add_left, polar_smul_left, hpp₁, smul_eq_mul, mul_one] at hc
  rw [polar_comm q u p₁, polar_comm q u' p₁, hp₁u, hp₁u', zero_add, zero_add] at hc
  rw [hc] at e'
  exact add_right_cancel e'

theorem polar_eq_one_of_finrank_eq_two (hq : q.polarBilin.Nondegenerate)
    {K : Submodule (ZMod 2) V} (hK : K ⊓ perp q K = ⊥)
    (h2 : finrank (ZMod 2) (perp q K) = 2) {x y : V} (hx : x ∈ perp q K) (hy : y ∈ perp q K)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) : polar q x y = 1 := by
  have hli : LinearIndependent (ZMod 2) ![x, y] := linearIndependent_pair_iff.mpr ⟨hx0, hy0, hxy⟩
  have hspan : Submodule.span (ZMod 2) {x, y} = perp q K := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_pair hli, h2])
    rw [Submodule.span_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  obtain ⟨z, hzK, hzx⟩ := exists_mem_perp_polar_eq_one hq hK hx hx0
  rw [← hspan] at hzK
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hzK
  rw [polar_add_left, polar_smul_left, polar_smul_left, polar_self_eq_zero, smul_zero,
    zero_add, smul_eq_mul] at hzx
  have h1 : polar q y x = 1 := by
    rcases zmod2_eq_zero_or_eq_one b with hb | hb
    · rw [hb, zero_mul] at hzx
      exact absurd hzx zero_ne_one
    · rwa [hb, one_mul] at hzx
  rw [polar_comm, h1]

end S2

end CFSG.LargeExtraspecial
