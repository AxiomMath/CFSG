module

public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def fixGroup (F : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ x ∈ F, g x = x}
  mul_mem' {g h} hg hh x hx := by rw [LinearEquiv.mul_apply, hh x hx, hg x hx]
  one_mem' _ _ := rfl
  inv_mem' {g} hg x hx := by
    conv_lhs => rw [← hg x hx]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' g x

theorem mem_fixGroup {F : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ fixGroup F ↔ ∀ x ∈ F, g x = x :=
  Iff.rfl

theorem fixGroup_bot : fixGroup (⊥ : Submodule (ZMod 2) V) = ⊤ := by
  ext g
  simp only [mem_fixGroup, Submodule.mem_bot, Subgroup.mem_top, iff_true]
  rintro x rfl
  exact map_zero g

theorem fixGroup_anti {F F' : Submodule (ZMod 2) V} (h : F ≤ F') : fixGroup F' ≤ fixGroup F :=
  fun _ hg x hx => hg x (h hx)

theorem mem_fixGroup_sup_span_pair {F : Submodule (ZMod 2) V} {p p₁ : V}
    {g : V ≃ₗ[ZMod 2] V} :
    g ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
      g ∈ fixGroup F ∧ g p = p ∧ g p₁ = p₁ := by
  constructor
  · intro hg
    exact ⟨fixGroup_anti le_sup_left hg,
      hg p (Submodule.mem_sup_right (Submodule.subset_span (by simp))),
      hg p₁ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩
  · rintro ⟨hF, hp, hp₁⟩ x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_add, map_smul, map_smul, hF y hy, hp, hp₁]

abbrev perp (q : QuadraticForm (ZMod 2) V) (F : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal q.polarBilin F

variable {q : QuadraticForm (ZMod 2) V}

theorem mem_perp {F : Submodule (ZMod 2) V} {x : V} :
    x ∈ perp q F ↔ ∀ y ∈ F, polar q y x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [polarBilin_apply_apply]

theorem perp_bot : perp q (⊥ : Submodule (ZMod 2) V) = ⊤ :=
  LinearMap.BilinForm.orthogonal_bot

theorem mem_perp_sup_span_pair {F : Submodule (ZMod 2) V} {p p₁ x : V} :
    x ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
      x ∈ perp q F ∧ polar q p x = 0 ∧ polar q p₁ x = 0 := by
  simp only [mem_perp]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Submodule.mem_sup_left hy),
      h p (Submodule.mem_sup_right (Submodule.subset_span (by simp))),
      h p₁ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩
  · rintro ⟨hF, hp, hp₁⟩ w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hF y hy, hp, hp₁]
    simp

theorem perp_sup_span_pair_le {F : Submodule (ZMod 2) V} {p p₁ : V} :
    perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ≤ perp q F :=
  fun _ hx => (mem_perp_sup_span_pair.mp hx).1

theorem sup_span_pair_inf_perp_eq_bot {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥)
    {p p₁ : V} (hp : p ∈ perp q F) (hp₁ : p₁ ∈ perp q F) (hpp₁ : polar q p p₁ = 1) :
    (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ⊓ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) =
      ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxp⟩
  obtain ⟨hxF, hxa, hxb⟩ := mem_perp_sup_span_pair.mp hxp
  obtain ⟨k, hk, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
  have hkp : polar q p k = 0 := by rw [polar_comm]; exact (mem_perp.mp hp) k hk
  have hkp₁ : polar q p₁ k = 0 := by rw [polar_comm]; exact (mem_perp.mp hp₁) k hk
  have hpp : polar q p p = 0 := polar_self_eq_zero q p
  have hp₁p₁ : polar q p₁ p₁ = 0 := polar_self_eq_zero q p₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, hkp, hpp, hpp₁]
    at hxa
  rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, hkp₁, hp₁p,
    hp₁p₁] at hxb
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] at hxa hxb
  subst hxa hxb
  simp only [zero_smul, add_zero] at hxF ⊢
  have : k ∈ F ⊓ perp q F := ⟨hk, hxF⟩
  rwa [hF] at this

theorem linearIndependent_of_polar_eq_one {p p₁ : V} (hpp₁ : polar q p p₁ = 1) :
    LinearIndependent (ZMod 2) ![p, p₁] := by
  refine linearIndependent_pair_iff.mpr ⟨?_, ?_, ?_⟩
  · rintro rfl
    rw [polar_zero_left] at hpp₁
    exact zero_ne_one hpp₁
  · rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  · rintro rfl
    rw [polar_self_eq_zero] at hpp₁
    exact zero_ne_one hpp₁

variable [FiniteDimensional (ZMod 2) V]

theorem sup_perp_eq_top {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) :
    F ⊔ perp q F = ⊤ :=
  ((LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (isRefl_polarBilin q)).mpr
    (disjoint_iff.mpr hF)).sup_eq_top

theorem exists_mem_perp_sub_mem {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (x : V) :
    ∃ y ∈ perp q F, x - y ∈ F := by
  have hx : x ∈ F ⊔ perp q F := by rw [sup_perp_eq_top hF]; exact Submodule.mem_top
  obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨y, hy, by rwa [add_sub_cancel_right]⟩

theorem exists_mem_perp_polar_eq {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (x : V) :
    ∃ y ∈ perp q F, ∀ v ∈ perp q F, polar q y v = polar q x v := by
  obtain ⟨y, hy, hxy⟩ := exists_mem_perp_sub_mem hF x
  refine ⟨y, hy, fun v hv => ?_⟩
  have h := (mem_perp.mp hv) _ hxy
  rw [polar_sub_left] at h
  exact (sub_eq_zero.mp h).symm

theorem exists_mem_perp_polar_eq_one (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {v : V} (hv : v ∈ perp q F)
    (hv0 : v ≠ 0) : ∃ y ∈ perp q F, polar q y v = 1 := by
  obtain ⟨x, hx⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hq hv0
  obtain ⟨y, hy, hyv⟩ := exists_mem_perp_polar_eq hF x
  refine ⟨y, hy, ?_⟩
  rw [hyv v hv, polar_comm]
  exact zmod2_eq_one_of_ne_zero hx

theorem exists_mem_perp_polar_eq_one_polar_eq_zero (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {v w : V} (hv : v ∈ perp q F)
    (hw : w ∈ perp q F) (hli : LinearIndependent (ZMod 2) ![v, w]) :
    ∃ x ∈ perp q F, polar q x v = 1 ∧ polar q x w = 0 := by
  obtain ⟨x, hxv, hxw⟩ := exists_polar_eq_one_polar_eq_zero hq hli
  obtain ⟨y, hy, hyx⟩ := exists_mem_perp_polar_eq hF x
  exact ⟨y, hy, by rw [hyx v hv, hxv], by rw [hyx w hw, hxw]⟩

theorem exists_mem_perp_polar_eq_one_polar_eq_one (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {v w : V} (hv : v ∈ perp q F)
    (hw : w ∈ perp q F) (hli : LinearIndependent (ZMod 2) ![v, w]) :
    ∃ x ∈ perp q F, polar q x v = 1 ∧ polar q x w = 1 := by
  obtain ⟨x, hx, hxv, hxw⟩ := exists_mem_perp_polar_eq_one_polar_eq_zero hq hF hv hw hli
  obtain ⟨y, hy, hyw, hyv⟩ :=
    exists_mem_perp_polar_eq_one_polar_eq_zero hq hF hw hv (linearIndependent_pair_symm hli)
  refine ⟨x + y, Submodule.add_mem _ hx hy, ?_, ?_⟩
  · rw [polar_add_left, hxv, hyv, add_zero]
  · rw [polar_add_left, hxw, hyw, zero_add]

theorem exists_mem_perp_map_eq_one (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (hne : perp q F ≠ ⊥) :
    ∃ c ∈ perp q F, q c = 1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨y, hy, hyv⟩ := exists_mem_perp_polar_eq_one hq hF hv hv0
  by_cases hqv : q v = 1
  · exact ⟨v, hv, hqv⟩
  by_cases hqy : q y = 1
  · exact ⟨y, hy, hqy⟩
  refine ⟨v + y, Submodule.add_mem _ hv hy, ?_⟩
  have hv' : q v = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right hqv
  have hy' : q y = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right hqy
  rw [map_add_eq, hv', hy', polar_comm, hyv]
  decide

theorem finrank_perp_sup_span_pair (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {p p₁ : V} (hp : p ∈ perp q F)
    (hp₁ : p₁ ∈ perp q F) (hpp₁ : polar q p p₁ = 1) :
    finrank (ZMod 2) (perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁})) + 2 =
      finrank (ZMod 2) (perp q F) := by
  have hspan : Submodule.span (ZMod 2) {p, p₁} ≤ perp q F := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hp
    · exact hp₁
  have hinf : F ⊓ Submodule.span (ZMod 2) {p, p₁} = ⊥ := by
    rw [eq_bot_iff, ← hF]
    exact inf_le_inf_left _ hspan
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F (Submodule.span (ZMod 2) {p, p₁})
  rw [hinf, finrank_bot, add_zero,
    finrank_span_pair (linearIndependent_of_polar_eq_one hpp₁)] at h1
  rw [LinearMap.BilinForm.finrank_orthogonal hq, LinearMap.BilinForm.finrank_orthogonal hq, h1]
  have h2 := Submodule.finrank_le (F ⊔ Submodule.span (ZMod 2) {p, p₁})
  omega

variable (q) in
@[expose] def omegaFix (hq : q.polarBilin.Nondegenerate) (F : Submodule (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) :=
  omegaGroup q hq ⊓ fixGroup F

theorem mem_omegaFix {hq : q.polarBilin.Nondegenerate} {F : Submodule (ZMod 2) V}
    {g : V ≃ₗ[ZMod 2] V} : g ∈ omegaFix q hq F ↔ g ∈ omegaGroup q hq ∧ g ∈ fixGroup F :=
  Iff.rfl

theorem omegaFix_bot (hq : q.polarBilin.Nondegenerate) : omegaFix q hq ⊥ = omegaGroup q hq := by
  rw [omegaFix, fixGroup_bot, inf_top_eq]

theorem mem_orthogonalGroup_of_mem_omegaFix {hq : q.polarBilin.Nondegenerate}
    {F : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ omegaFix q hq F) :
    g ∈ orthogonalGroup q :=
  (mem_omegaGroup.mp hg.1).1

theorem mem_omegaFix_sup_span_pair {hq : q.polarBilin.Nondegenerate}
    {F : Submodule (ZMod 2) V} {p p₁ : V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ omegaFix q hq (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
      g ∈ omegaFix q hq F ∧ g p = p ∧ g p₁ = p₁ := by
  rw [mem_omegaFix, mem_omegaFix, mem_fixGroup_sup_span_pair]
  tauto

variable (q) in
@[expose] def radFix (F : Submodule (ZMod 2) V) (p : V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  pointRadical q p ⊓ fixGroup F

omit [FiniteDimensional (ZMod 2) V] in
theorem radFix_bot (p : V) : radFix q ⊥ p = pointRadical q p := by
  rw [radFix, fixGroup_bot, inf_top_eq]

omit [FiniteDimensional (ZMod 2) V] in
theorem radFix_le_pointRadical (F : Submodule (ZMod 2) V) (p : V) :
    radFix q F p ≤ pointRadical q p :=
  inf_le_left

omit [FiniteDimensional (ZMod 2) V] in
theorem radFix_anti {F F' : Submodule (ZMod 2) V} (h : F ≤ F') (p : V) :
    radFix q F' p ≤ radFix q F p :=
  inf_le_inf_left _ (fixGroup_anti h)

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_perp {F : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup q) (hgF : g ∈ fixGroup F) {x : V} (hx : x ∈ perp q F) :
    g x ∈ perp q F := by
  rw [mem_perp] at hx ⊢
  intro y hy
  rw [← hgF y hy, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg]
  exact hx y hy

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_mem_fixGroup {F : Submodule (ZMod 2) V} {p u : V} (hp : p ∈ perp q F)
    (hu : u ∈ perp q F) : eichler q p u ∈ fixGroup F := fun x hx =>
  CFSG.ClassicalGroups.Orthogonal.eichler_apply_of_polar_eq_zero ((mem_perp.mp hp) x hx)
    ((mem_perp.mp hu) x hx)

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_self {u : V} (hu : q u = 0) : eichler q u u = 1 := by
  have h := CFSG.ClassicalGroups.Orthogonal.eichler_add_smul_self (Q := q) hu 0 1
  rwa [zero_add, one_smul, eichler_zero_right] at h

theorem eichler_mem_omegaGroup (hq : q.polarBilin.Nondegenerate) (u w : V) :
    eichler q u w ∈ omegaGroup q hq := by
  refine mem_omegaGroup.mpr ⟨eichler_mem_orthogonalGroup q u w, ?_⟩
  by_cases h : q u = 0 ∧ polar q u w = 0
  · by_cases hli : LinearIndependent (ZMod 2) ![u, w]
    · rw [commSpace_eichler hq h.1 h.2 hli, finrank_span_pair hli]
      exact even_two
    · have h1 : eichler q u w = 1 := by
        rw [linearIndependent_pair_iff] at hli
        by_cases hu : u = 0
        · subst hu
          exact CFSG.ClassicalGroups.Orthogonal.eichler_zero_left q w
        by_cases hw : w = 0
        · subst hw
          exact eichler_zero_right q u
        have huw : u = w := by
          by_contra huw
          exact hli ⟨hu, hw, huw⟩
        subst huw
        exact eichler_self h.1
      rw [h1, commSpace_one, finrank_bot]
      exact ⟨0, rfl⟩
  · rw [CFSG.ClassicalGroups.Orthogonal.eichler_of_not h, commSpace_one, finrank_bot]
    exact ⟨0, rfl⟩

theorem pointRadical_le_omegaGroup (hq : q.polarBilin.Nondegenerate) {p : V} (hp0 : p ≠ 0)
    (hp : q p = 0) : pointRadical q p ≤ omegaGroup q hq := by
  intro t ht
  obtain ⟨u, -, rfl⟩ := (mem_pointRadical_iff hq hp0 hp).mp ht
  exact eichler_mem_omegaGroup hq p u

theorem radFix_le_omegaFix (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V} {p : V}
    (hp0 : p ≠ 0) (hp : q p = 0) : radFix q F p ≤ omegaFix q hq F :=
  fun _ ht => ⟨pointRadical_le_omegaGroup hq hp0 hp ht.1, ht.2⟩

theorem mem_radFix_iff (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V} {p : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hpF : p ∈ perp q F) {t : V ≃ₗ[ZMod 2] V} :
    t ∈ radFix q F p ↔ ∃ u ∈ perp q F, polar q p u = 0 ∧ t = eichler q p u := by
  constructor
  · rintro ⟨ht, htF⟩
    obtain ⟨u, hpu, rfl⟩ := (mem_pointRadical_iff hq hp0 hp).mp ht
    refine ⟨u, mem_perp.mpr fun x hx => ?_, hpu, rfl⟩
    have h := htF x hx
    rw [eichler_apply_zmod2 hp hpu, (mem_perp.mp hpF) x hx] at h
    simp only [zero_smul, mul_zero, add_zero, add_eq_left, smul_eq_zero, hp0, or_false] at h
    exact h
  · rintro ⟨u, huF, hpu, rfl⟩
    exact ⟨eichler_mem_pointRadical hp hpu, eichler_mem_fixGroup hpF huF⟩

theorem conj_mem_radFix (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V} {p : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hpF : p ∈ perp q F) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup q) (hgF : g ∈ fixGroup F) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ radFix q F p) : g * t * g⁻¹ ∈ radFix q F (g p) := by
  obtain ⟨u, huF, hpu, rfl⟩ := (mem_radFix_iff hq hp0 hp hpF).mp ht
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_conj hg]
  have hgp0 : g p ≠ 0 := fun h => hp0 (g.map_eq_zero_iff.mp h)
  have hgp : q (g p) = 0 := by rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hp]
  refine (mem_radFix_iff hq hgp0 hgp (apply_mem_perp hg hgF hpF)).mpr
    ⟨g u, apply_mem_perp hg hgF huF, ?_, rfl⟩
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, hpu]

theorem map_conj_radFix (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V} {p : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hpF : p ∈ perp q F) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup q) (hgF : g ∈ fixGroup F) (x : V ≃ₗ[ZMod 2] V) :
    x ∈ radFix q F (g p) ↔ g⁻¹ * x * g ∈ radFix q F p := by
  constructor
  · intro hx
    have hgp0 : g p ≠ 0 := fun h => hp0 (g.map_eq_zero_iff.mp h)
    have hgp : q (g p) = 0 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hp]
    have h := conj_mem_radFix hq hgp0 hgp (apply_mem_perp hg hgF hpF) (inv_mem hg)
      (inv_mem hgF) hx
    rwa [inv_inv, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'] at h
  · intro hx
    have h := conj_mem_radFix hq hp0 hp hpF hg hgF hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_apply_of_polar_eq_one {p p₁ w : V} (hp : q p = 0) (hpw : polar q p w = 0)
    (hpp₁ : polar q p p₁ = 1) :
    eichler q p w p₁ = p₁ + w + (polar q p₁ w + q w) • p := by
  rw [eichler_apply_zmod2 hp hpw, polar_comm q p₁ p, hpp₁, one_smul, mul_one]

theorem exists_mem_radFix_apply_eq (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p p₁ p₁' : V} (hp0 : p ≠ 0) (hp : q p = 0) (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hp₁'F : p₁' ∈ perp q F) (hqp₁ : q p₁ = 0) (hqp₁' : q p₁' = 0)
    (hpp₁ : polar q p p₁ = 1) (hpp₁' : polar q p p₁' = 1) :
    ∃ t ∈ radFix q F p, t p₁ = p₁' := by
  set w := p₁' - p₁ with hw
  have hpw : polar q p w = 0 := by rw [hw, polar_sub_right, hpp₁, hpp₁', sub_self]
  refine ⟨eichler q p w, (mem_radFix_iff hq hp0 hp hpF).mpr
    ⟨w, Submodule.sub_mem _ hp₁'F hp₁F, hpw, rfl⟩, ?_⟩
  have hp₁' : p₁' = p₁ + w := by rw [hw]; abel
  have hc : polar q p₁ w + q w = 0 := by
    have h := hqp₁'
    rw [hp₁', map_add_eq, hqp₁, zero_add] at h
    rw [add_comm]
    exact h
  rw [eichler_apply_of_polar_eq_one hp hpw hpp₁, hc, zero_smul, add_zero, ← hp₁']

theorem eq_one_of_mem_pointRadical_of_apply_eq (hq : q.polarBilin.Nondegenerate) {p p₁ : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ pointRadical q p) (htp₁ : t p₁ = p₁) : t = 1 := by
  obtain ⟨u, hpu, rfl⟩ := (mem_pointRadical_iff hq hp0 hp).mp ht
  rw [eichler_apply_of_polar_eq_one hp hpu hpp₁, add_assoc, add_eq_left] at htp₁
  refine (eichler_eq_one_iff hq hp0 hp hpu).mpr ?_
  rw [add_eq_zero_iff_eq_neg, vec_neg] at htp₁
  rw [htp₁]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)

theorem pointRadical_inf_eq_bot (hq : q.polarBilin.Nondegenerate) {p p₁ : V} (hp0 : p ≠ 0)
    (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) : pointRadical q p ⊓ pointRadical q p₁ = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨ht, ht₁⟩
  exact (Subgroup.mem_bot).mpr (eq_one_of_mem_pointRadical_of_apply_eq hq hp0 hp hpp₁ ht ht₁.2.1)

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_comm {p p' : V} (hp : q p = 0) (hp' : q p' = 0) (hpp' : polar q p p' = 0) :
    eichler q p p' = eichler q p' p := by
  have hp'p : polar q p' p = 0 := by rw [polar_comm, hpp']
  ext x
  rw [eichler_apply_zmod2 hp hpp', eichler_apply_zmod2 hp' hp'p, hp, hp']
  simp only [zero_mul, add_zero]
  abel

theorem mem_pointRadical_inf_of_orthogonal (hq : q.polarBilin.Nondegenerate) {p p' : V}
    (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (hpp' : p ≠ p') (hp : q p = 0) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ pointRadical q p ⊓ pointRadical q p') :
    t = 1 ∨ t = eichler q p p' := by
  obtain ⟨ht, -, -, ht'1, -⟩ := ht
  obtain ⟨u, hpu, rfl⟩ := (mem_pointRadical_iff hq hp0 hp).mp ht
  have hli : LinearIndependent (ZMod 2) ![p, p'] := linearIndependent_pair_iff.mpr ⟨hp0, hp'0, hpp'⟩
  obtain ⟨x, hxp, hxp'⟩ := exists_polar_eq_one_polar_eq_zero hq hli
  have h := ht'1 x (by rw [polar_comm]; exact hxp')
  rw [eichler_apply_zmod2 hp hpu, hxp, one_smul, mul_one, add_assoc, add_sub_cancel_left] at h
  rcases mem_span_singleton_iff.mp h with h0 | h0
  · left
    refine (eichler_eq_one_iff hq hp0 hp hpu).mpr ?_
    rw [add_eq_zero_iff_eq_neg, vec_neg] at h0
    rw [h0]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)
  · right
    have hu : u = p' + (polar q x u + q u) • p := by
      rw [← h0, add_assoc, vec_add_self, add_zero]
    rw [hu, CFSG.ClassicalGroups.Orthogonal.eichler_add_smul_self hp]

omit [FiniteDimensional (ZMod 2) V] in
theorem eichler_mem_pointRadical_inf {p p' : V} (hp : q p = 0) (hp' : q p' = 0)
    (hpp' : polar q p p' = 0) : eichler q p p' ∈ pointRadical q p ⊓ pointRadical q p' := by
  have hp'p : polar q p' p = 0 := by rw [polar_comm, hpp']
  refine ⟨eichler_mem_pointRadical hp hpp', ?_⟩
  rw [eichler_comm hp hp' hpp']
  exact eichler_mem_pointRadical hp' hp'p

end S2

end CFSG.LargeExtraspecial
