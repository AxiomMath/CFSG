module

public import CFSG.LargeExtraspecial.S2SpGeom
public import CFSG.LargeExtraspecial.S2OrthGeom

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}

abbrev spPerp (f : BilinForm (ZMod 2) V) (F : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  f.orthogonal F

theorem mem_spPerp {F : Submodule (ZMod 2) V} {x : V} : x ∈ spPerp f F ↔ ∀ y ∈ F, f y x = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem spPerp_bot : spPerp f (⊥ : Submodule (ZMod 2) V) = ⊤ :=
  LinearMap.BilinForm.orthogonal_bot

theorem mem_spPerp_sup_span_pair {F : Submodule (ZMod 2) V} {p p₁ x : V} :
    x ∈ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
      x ∈ spPerp f F ∧ f p x = 0 ∧ f p₁ x = 0 := by
  simp only [mem_spPerp]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Submodule.mem_sup_left hy),
      h p (Submodule.mem_sup_right (Submodule.subset_span (by simp))),
      h p₁ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))⟩
  · rintro ⟨hF, hp, hp₁⟩ w hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hF y hy, hp, hp₁,
      smul_zero, add_zero]

theorem spPerp_sup_span_pair_le {F : Submodule (ZMod 2) V} {p p₁ : V} :
    spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ≤ spPerp f F :=
  fun _ hx => (mem_spPerp_sup_span_pair.mp hx).1

theorem sup_span_pair_inf_spPerp_eq_bot (hf : f.IsAlt) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {p p₁ : V} (hp : p ∈ spPerp f F) (hp₁ : p₁ ∈ spPerp f F)
    (hpp₁ : f p p₁ = 1) :
    (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ⊓ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) =
      ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxp⟩
  obtain ⟨hxF, hxa, hxb⟩ := mem_spPerp_sup_span_pair.mp hxp
  obtain ⟨k, hk, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
  have hkp : f p k = 0 := by rw [isAlt_symm hf]; exact (mem_spPerp.mp hp) k hk
  have hkp₁ : f p₁ k = 0 := by rw [isAlt_symm hf]; exact (mem_spPerp.mp hp₁) k hk
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  simp only [map_add, map_smul, hkp, hkp₁, hf.self_eq_zero, hpp₁, hp₁p, smul_eq_mul, mul_zero,
    mul_one, zero_add, add_zero] at hxa hxb
  subst hxa hxb
  simp only [zero_smul, add_zero] at hxF ⊢
  have : k ∈ F ⊓ spPerp f F := ⟨hk, hxF⟩
  rwa [hF] at this

theorem linearIndependent_of_apply_eq_one (hf : f.IsAlt) {p p₁ : V} (hpp₁ : f p p₁ = 1) :
    LinearIndependent (ZMod 2) ![p, p₁] := by
  refine linearIndependent_pair_iff.mpr ⟨?_, ?_, ?_⟩
  · rintro rfl
    rw [map_zero, LinearMap.zero_apply] at hpp₁
    exact zero_ne_one hpp₁
  · rintro rfl
    rw [map_zero] at hpp₁
    exact zero_ne_one hpp₁
  · rintro rfl
    rw [hf.self_eq_zero] at hpp₁
    exact zero_ne_one hpp₁

variable [FiniteDimensional (ZMod 2) V]

theorem exists_mem_spPerp_sub_mem (hf : f.IsAlt) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) (x : V) : ∃ y ∈ spPerp f F, x - y ∈ F := by
  have htop : F ⊔ spPerp f F = ⊤ :=
    ((LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hf.isRefl).mpr
      (disjoint_iff.mpr hF)).sup_eq_top
  have hx : x ∈ F ⊔ spPerp f F := by rw [htop]; exact Submodule.mem_top
  obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨y, hy, by rwa [add_sub_cancel_right]⟩

theorem exists_mem_spPerp_apply_eq (hf : f.IsAlt) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) (x : V) :
    ∃ y ∈ spPerp f F, ∀ v ∈ spPerp f F, f y v = f x v := by
  obtain ⟨y, hy, hxy⟩ := exists_mem_spPerp_sub_mem hf hF x
  refine ⟨y, hy, fun v hv => ?_⟩
  have h := (mem_spPerp.mp hv) _ hxy
  rw [map_sub, LinearMap.sub_apply] at h
  exact (sub_eq_zero.mp h).symm

theorem exists_mem_spPerp_apply_eq_one (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {v : V} (hv : v ∈ spPerp f F)
    (hv0 : v ≠ 0) : ∃ y ∈ spPerp f F, f y v = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, f x v ≠ 0 := by
    by_contra! h
    exact hv0 (hnd.2 v h)
  obtain ⟨y, hy, hyx⟩ := exists_mem_spPerp_apply_eq hf hF x
  exact ⟨y, hy, by rw [hyx v hv]; exact zmod2_eq_one_of_ne_zero hx⟩

theorem exists_mem_spPerp_eq_one_eq_zero (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {v w : V} (hv : v ∈ spPerp f F)
    (hw : w ∈ spPerp f F) (hli : LinearIndependent (ZMod 2) ![v, w]) :
    ∃ x ∈ spPerp f F, f x v = 1 ∧ f x w = 0 := by
  obtain ⟨x, hxv, hxw⟩ := sp_exists_dual hf hnd hli
  obtain ⟨y, hy, hyx⟩ := exists_mem_spPerp_apply_eq hf hF x
  exact ⟨y, hy, by rw [hyx v hv, hxv], by rw [hyx w hw, hxw]⟩

theorem exists_mem_spPerp_eq_one_eq_one (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {v w : V} (hv : v ∈ spPerp f F)
    (hw : w ∈ spPerp f F) (hli : LinearIndependent (ZMod 2) ![v, w]) :
    ∃ x ∈ spPerp f F, f x v = 1 ∧ f x w = 1 := by
  obtain ⟨x, hx, hxv, hxw⟩ := exists_mem_spPerp_eq_one_eq_zero hf hnd hF hv hw hli
  obtain ⟨y, hy, hyw, hyv⟩ :=
    exists_mem_spPerp_eq_one_eq_zero hf hnd hF hw hv (linearIndependent_pair_symm hli)
  refine ⟨x + y, Submodule.add_mem _ hx hy, ?_, ?_⟩
  · rw [map_add, LinearMap.add_apply, hxv, hyv, add_zero]
  · rw [map_add, LinearMap.add_apply, hxw, hyw, zero_add]

theorem finrank_spPerp_sup_span_pair (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p p₁ : V} (hp : p ∈ spPerp f F)
    (hp₁ : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) :
    finrank (ZMod 2) (spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁})) + 2 =
      finrank (ZMod 2) (spPerp f F) := by
  have hspan : Submodule.span (ZMod 2) {p, p₁} ≤ spPerp f F := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hp
    · exact hp₁
  have hinf : F ⊓ Submodule.span (ZMod 2) {p, p₁} = ⊥ := by
    rw [eq_bot_iff, ← hF]
    exact inf_le_inf_left _ hspan
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F (Submodule.span (ZMod 2) {p, p₁})
  rw [hinf, finrank_bot, add_zero,
    finrank_span_pair (linearIndependent_of_apply_eq_one hf hpp₁)] at h1
  rw [LinearMap.BilinForm.finrank_orthogonal hnd, LinearMap.BilinForm.finrank_orthogonal hnd, h1]
  have h2 := Submodule.finrank_le (F ⊔ Submodule.span (ZMod 2) {p, p₁})
  omega

variable (f) in
@[expose] def spFix (F : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  TauCeti.BilinForm.isometryGroup f ⊓ fixGroup F

omit [FiniteDimensional (ZMod 2) V] in
theorem spFix_bot : spFix f ⊥ = TauCeti.BilinForm.isometryGroup f := by
  rw [spFix, fixGroup_bot, inf_top_eq]

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_spFix_sup_span_pair {F : Submodule (ZMod 2) V} {p p₁ : V} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ spFix f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔ g ∈ spFix f F ∧ g p = p ∧ g p₁ = p₁ := by
  simp only [spFix, Subgroup.mem_inf, mem_fixGroup_sup_span_pair]
  tauto

variable (f) in
@[expose] def spRadFix (F : Submodule (ZMod 2) V) (p : V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  spPointRadical f p ⊓ fixGroup F

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadFix_bot (p : V) : spRadFix f ⊥ p = spPointRadical f p := by
  rw [spRadFix, fixGroup_bot, inf_top_eq]

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadFix_anti {F F' : Submodule (ZMod 2) V} (h : F ≤ F') (p : V) :
    spRadFix f F' p ≤ spRadFix f F p :=
  inf_le_inf_left _ (fixGroup_anti h)

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadFix_le_spFix (F : Submodule (ZMod 2) V) (p : V) : spRadFix f F p ≤ spFix f F :=
  fun _ ht => ⟨ht.1.1, ht.2⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_spPerp {F : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup f) (hgF : g ∈ fixGroup F) {x : V}
    (hx : x ∈ spPerp f F) : g x ∈ spPerp f F := by
  rw [mem_spPerp] at hx ⊢
  intro y hy
  rw [← hgF y hy, TauCeti.BilinForm.mem_isometryGroup_iff.mp hg]
  exact hx y hy

omit [FiniteDimensional (ZMod 2) V] in
theorem spSiegel_mem_fixGroup (hf : f.IsAlt) {F : Submodule (ZMod 2) V} {p u : V}
    (hpF : p ∈ spPerp f F) (huF : u ∈ spPerp f F) (c : ZMod 2) :
    spSiegel f hf p u c ∈ fixGroup F := by
  intro x hx
  by_cases hpu : f p u = 0
  · rw [spSiegel_apply hf hpu, (mem_spPerp.mp hpF) x hx, (mem_spPerp.mp huF) x hx]
    simp
  · rw [spSiegel, dite_eq_right hpu]
    rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_spRadFix_iff (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p : V} (hp0 : p ≠ 0) (hpF : p ∈ spPerp f F) {t : V ≃ₗ[ZMod 2] V} :
    t ∈ spRadFix f F p ↔ ∃ u ∈ spPerp f F, f p u = 0 ∧ ∃ c, t = spSiegel f hf p u c := by
  constructor
  · rintro ⟨ht, htF⟩
    obtain ⟨u, hpu, c, rfl⟩ := (mem_spPointRadical_iff hf hnd hp0).mp ht
    refine ⟨u, mem_spPerp.mpr fun x hx => ?_, hpu, c, rfl⟩
    have h := htF x hx
    rw [spSiegel_apply hf hpu, (mem_spPerp.mp hpF) x hx] at h
    simp only [zero_smul, mul_zero, add_zero, add_eq_left, smul_eq_zero, hp0, or_false] at h
    exact h
  · rintro ⟨u, huF, hpu, c, rfl⟩
    exact ⟨spSiegel_mem_spPointRadical hf hpu c, spSiegel_mem_fixGroup hf hpF huF c⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem map_conj_spRadFix (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p : V} (hp0 : p ≠ 0) (hpF : p ∈ spPerp f F) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup f) (hgF : g ∈ fixGroup F) (x : V ≃ₗ[ZMod 2] V) :
    x ∈ spRadFix f F (g p) ↔ g⁻¹ * x * g ∈ spRadFix f F p := by
  have hgp0 : g p ≠ 0 := fun h => hp0 (g.map_eq_zero_iff.mp h)
  have hgpF := apply_mem_spPerp hg hgF hpF
  have hconj : ∀ {a : V} {k : V ≃ₗ[ZMod 2] V}, a ≠ 0 → a ∈ spPerp f F →
      k ∈ TauCeti.BilinForm.isometryGroup f → k ∈ fixGroup F → ∀ t ∈ spRadFix f F a,
      k * t * k⁻¹ ∈ spRadFix f F (k a) := by
    intro a k ha0 haF hk hkF t ht
    obtain ⟨u, huF, hau, c, rfl⟩ := (mem_spRadFix_iff hf hnd ha0 haF).mp ht
    rw [spSiegel_conj hf hk hau]
    have hka : f (k a) (k u) = 0 := by rw [TauCeti.BilinForm.mem_isometryGroup_iff.mp hk, hau]
    exact (mem_spRadFix_iff hf hnd (fun h => ha0 (k.map_eq_zero_iff.mp h))
      (apply_mem_spPerp hk hkF haF)).mpr ⟨k u, apply_mem_spPerp hk hkF huF, hka, c, rfl⟩
  constructor
  · intro hx
    have h := hconj hgp0 hgpF (inv_mem hg) (inv_mem hgF) x hx
    rwa [inv_inv, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply'] at h
  · intro hx
    have h := hconj hp0 hpF hg hgF _ hx
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_mem_spRadFix_apply_eq (hf : f.IsAlt) {F : Submodule (ZMod 2) V} {p p₁ p₁' : V}
    (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hp₁'F : p₁' ∈ spPerp f F)
    (hpp₁ : f p p₁ = 1) (hpp₁' : f p p₁' = 1) : ∃ t ∈ spRadFix f F p, t p₁ = p₁' := by
  set w := p₁' - p₁ with hw
  have hpw : f p w = 0 := by rw [hw, map_sub, hpp₁, hpp₁', sub_self]
  have hwF : w ∈ spPerp f F := Submodule.sub_mem _ hp₁'F hp₁F
  refine ⟨spSiegel f hf p w (f p₁ w), ⟨spSiegel_mem_spPointRadical hf hpw _,
    spSiegel_mem_fixGroup hf hpF hwF _⟩, ?_⟩
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  rw [spSiegel_apply hf hpw, hp₁p, one_smul, mul_one, zmod2_add_self, zero_smul, add_zero, hw,
    add_sub_cancel]

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_one_of_mem_spPointRadical_of_apply_eq {p p₁ : V} (hpp₁ : f p p₁ = 1)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ spPointRadical f p) (htp₁ : t p₁ = p₁) : t = 1 :=
  spPointRadical_ext hpp₁ ht (one_mem _) (by rw [htp₁]; rfl)

omit [FiniteDimensional (ZMod 2) V] in
theorem spPointRadical_inf_eq_bot {p p₁ : V} (hpp₁ : f p p₁ = 1) :
    spPointRadical f p ⊓ spPointRadical f p₁ = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨ht, ht₁⟩
  exact (Subgroup.mem_bot).mpr (eq_one_of_mem_spPointRadical_of_apply_eq hpp₁ ht ht₁.2.1)

theorem mem_spPointRadical_inf (hf : f.IsAlt) (hnd : f.Nondegenerate) {p p' : V} (hp0 : p ≠ 0)
    (hp'0 : p' ≠ 0) (hpp' : p ≠ p') {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ spPointRadical f p ⊓ spPointRadical f p') : t = 1 ∨ t = spSiegel f hf p p' 0 := by
  obtain ⟨ht, ht'⟩ := ht
  have hli : LinearIndependent (ZMod 2) ![p, p'] :=
    linearIndependent_pair_iff.mpr ⟨hp0, hp'0, hpp'⟩
  obtain ⟨x, hxp, hxp'⟩ := sp_exists_dual hf hnd hli
  have hpx : f p x = 1 := by rw [isAlt_symm hf, hxp]
  have h := ht'.2.2.1 x (by rw [isAlt_symm hf, hxp'])
  rcases mem_span_singleton_iff.mp h with h0 | h1
  · left
    exact spPointRadical_ext hpx ht (one_mem _) (by rw [sub_eq_zero] at h0; rw [h0]; rfl)
  · by_cases hpp'0 : f p p' = 0
    · right
      refine spPointRadical_ext hpx ht (spSiegel_mem_spPointRadical hf hpp'0 0) ?_
      rw [spSiegel_apply hf hpp'0, hxp, hxp', one_smul, zero_mul, add_zero, zero_smul, add_zero,
        ← h1]
      abel
    · exfalso
      have h1' := ht'.2.1
      have hpp'1 : f p p' = 1 := zmod2_eq_one_of_ne_zero hpp'0
      exact absurd (eq_one_of_mem_spPointRadical_of_apply_eq hpp'1 ht h1') (fun h => by
        rw [h, LinearEquiv.coe_one, id, sub_self] at h1
        exact hp'0 h1.symm)

end S2

end CFSG.LargeExtraspecial
