module

public import CFSG.LargeExtraspecial.S2SpLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem sp_sub_mem_spPerp_sup_span_pair (hf : f.IsAlt) {F : Submodule (ZMod 2) V} {p p₁ : V}
    (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) {x : V}
    (hx : x ∈ spPerp f F) :
    x - f x p₁ • p - f x p • p₁ ∈ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) := by
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  refine mem_spPerp_sup_span_pair.mpr ⟨Submodule.sub_mem _ (Submodule.sub_mem _ hx
    (Submodule.smul_mem _ _ hpF)) (Submodule.smul_mem _ _ hp₁F), ?_, ?_⟩
  · rw [map_sub, map_sub, map_smul, map_smul, hf.self_eq_zero, hpp₁, isAlt_symm hf p x]
    simp
  · rw [map_sub, map_sub, map_smul, map_smul, hp₁p, hf.self_eq_zero, isAlt_symm hf p₁ x]
    simp

theorem sp_fixed_mem_span_of_spRadFix (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p : V} (hpF : p ∈ spPerp f F)
    (hp0 : p ≠ 0) {x : V} (hx : x ∈ spPerp f F) (hfix : ∀ t ∈ spRadFix f F p, t x = x) :
    x ∈ (ZMod 2) ∙ p := by
  obtain ⟨p₁, hp₁F, hpp₁⟩ := sp_exists_partner hf hnd hF hpF hp0
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ spPerp f K = ⊥ := sup_span_pair_inf_spPerp_eq_bot hf hF hpF hp₁F hpp₁
  have hzero : ∀ {a : V}, f a 0 = 0 := fun {a} => map_zero _
  have hxp : f x p = 0 := by
    have h := hfix _ ((mem_spRadFix_iff hf hnd hp0 hpF).mpr ⟨0, Submodule.zero_mem _, hzero, 1,
      rfl⟩)
    rw [spSiegel_apply hf hzero, smul_zero, add_zero, map_zero, zero_add, one_mul,
      add_eq_left, smul_eq_zero] at h
    exact h.resolve_right hp0
  have hx0 := sp_sub_mem_spPerp_sup_span_pair hf hpF hp₁F hpp₁ hx
  set x₀ := x - f x p₁ • p - f x p • p₁ with hx₀
  have hx₀0 : x₀ = 0 := by
    by_contra hne
    obtain ⟨y, hyK, hyx⟩ := exists_mem_spPerp_apply_eq_one hf hnd hK hx0 hne
    obtain ⟨hyF, hpy, hp₁y⟩ := mem_spPerp_sup_span_pair.mp hyK
    have h := hfix _ ((mem_spRadFix_iff hf hnd hp0 hpF).mpr ⟨y, hyF, hpy, 0, rfl⟩)
    rw [spSiegel_apply hf hpy, hxp, zero_smul, add_zero, zero_mul, add_zero, add_eq_left,
      smul_eq_zero] at h
    rcases h with h | h
    · have : f x₀ y = f x y := by
        rw [hx₀, map_sub, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.smul_apply, hpy, hp₁y]
        simp
      rw [isAlt_symm hf, this, h] at hyx
      exact zero_ne_one hyx
    · exact hp0 h
  have : x = f x p₁ • p := by
    rw [hx₀, hxp, zero_smul, sub_zero, sub_eq_zero] at hx₀0
    exact hx₀0
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)

theorem sp_eq_of_spRadFix_eq (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {p p' : V} (hpF : p ∈ spPerp f F) (hp'F : p' ∈ spPerp f F)
    (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (h : spRadFix f F p = spRadFix f F p') : p = p' := by
  have hmem : p' ∈ (ZMod 2) ∙ p := by
    refine sp_fixed_mem_span_of_spRadFix hf hnd hF hpF hp0 hp'F fun t ht => ?_
    rw [h] at ht
    exact ht.1.2.1
  rcases mem_span_singleton_iff.mp hmem with h0 | h1
  · exact absurd h0 hp'0
  · exact h1.symm

theorem mem_normalizer_spRadFix_iff (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p : V} (hpF : p ∈ spPerp f F)
    (hp0 : p ≠ 0) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ spFix f F) :
    g ∈ Subgroup.normalizer (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ↔ g p = p := by
  constructor
  · intro hN
    have hgpF : g p ∈ spPerp f F := apply_mem_spPerp hg.1 hg.2 hpF
    have hgp0 : g p ≠ 0 := fun h => hp0 (g.map_eq_zero_iff.mp h)
    refine sp_eq_of_spRadFix_eq hf hnd hF hgpF hpF hgp0 hp0 ?_
    ext x
    rw [map_conj_spRadFix hf hnd hp0 hpF hg.1 hg.2 x]
    rw [Subgroup.mem_normalizer_iff''] at hN
    exact (hN x).symm
  · intro hgp
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    have := map_conj_spRadFix hf hnd hp0 hpF hg.1 hg.2 x
    rw [hgp] at this
    exact this

theorem sp_timmesfeld_2_1_b1 (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F)
    (hpp₁ : f p p₁ = 1) :
    (∀ g, g ∈ spFix f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
      g ∈ spFix f F ∧ g ∈ Subgroup.normalizer (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ∧
        g ∈ Subgroup.normalizer (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V))) ∧
    (∀ g ∈ spFix f F, g ∈ Subgroup.normalizer (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) →
      ∃ t ∈ spRadFix f F p, ∃ y ∈ spFix f (F ⊔ Submodule.span (ZMod 2) {p, p₁}), g = t * y) ∧
    spRadFix f F p ⊓ spFix f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) = ⊥ := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  refine ⟨fun g => ?_, fun g hg hN => ?_, spRadFix_inf_spFix_eq_bot hpp₁⟩
  · rw [mem_spFix_sup_span_pair]
    constructor
    · rintro ⟨hg, hgp, hgp₁⟩
      exact ⟨hg, (mem_normalizer_spRadFix_iff hf hnd hF hpF hp0 hg).mpr hgp,
        (mem_normalizer_spRadFix_iff hf hnd hF hp₁F hp₁0 hg).mpr hgp₁⟩
    · rintro ⟨hg, hN, hN₁⟩
      exact ⟨hg, (mem_normalizer_spRadFix_iff hf hnd hF hpF hp0 hg).mp hN,
        (mem_normalizer_spRadFix_iff hf hnd hF hp₁F hp₁0 hg).mp hN₁⟩
  · have hgp := (mem_normalizer_spRadFix_iff hf hnd hF hpF hp0 hg).mp hN
    obtain ⟨t, ht, hty⟩ := exists_mem_spRadFix_inv_mul_mem hf hpF hp₁F hpp₁ hg hgp
    exact ⟨t, ht, t⁻¹ * g, hty, by group⟩

theorem spRadFix_inf_eq_bot_iff (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p p' : V} (hpF : p ∈ spPerp f F) (hp'F : p' ∈ spPerp f F)
    (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (hpp' : p ≠ p') :
    spRadFix f F p ⊓ spRadFix f F p' = ⊥ ↔ f p p' = 1 := by
  constructor
  · intro h
    by_contra hne
    have h0 : f p p' = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right hne
    have h0' : f p' p = 0 := by rw [isAlt_symm hf, h0]
    have hli : LinearIndependent (ZMod 2) ![p, p'] :=
      linearIndependent_pair_iff.mpr ⟨hp0, hp'0, hpp'⟩
    have hsymm : spSiegel f hf p p' 0 = spSiegel f hf p' p 0 := by
      ext x
      rw [spSiegel_apply hf h0, spSiegel_apply hf h0']
      simp only [zero_mul, add_zero]
      abel
    have hmem : spSiegel f hf p p' 0 ∈ spRadFix f F p ⊓ spRadFix f F p' :=
      ⟨(mem_spRadFix_iff hf hnd hp0 hpF).mpr ⟨p', hp'F, h0, 0, rfl⟩,
        (mem_spRadFix_iff hf hnd hp'0 hp'F).mpr ⟨p, hpF, h0', 0, hsymm⟩⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (isSpTypeA_spSiegel_zero hf hnd h0 hli).2.1 hmem
  · intro h
    rw [eq_bot_iff]
    rintro t ⟨ht, ht'⟩
    have := spPointRadical_inf_eq_bot h
    rw [eq_bot_iff] at this
    exact this ⟨ht.1, ht'.1⟩

theorem sp_normalizer_inf_spRadFix_eq_bot (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p p₁ : V} (hp₁F : p₁ ∈ spPerp f F)
    (hpp₁ : f p p₁ = 1) :
    spRadFix f F p ⊓ Subgroup.normalizer (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V)) = ⊥ := by
  obtain ⟨-, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  rw [eq_bot_iff]
  rintro t ⟨ht, hN⟩
  have htp₁ := (mem_normalizer_spRadFix_iff hf hnd hF hp₁F hp₁0
    (spRadFix_le_spFix F p ht)).mp hN
  exact (Subgroup.mem_bot).mpr (eq_one_of_mem_spPointRadical_of_apply_eq hpp₁ ht.1 htp₁)

theorem exists_mem_spRadGen_apply_eq_orth (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p p₂ p' p₂' : V}
    (hpF : p ∈ spPerp f F) (hp₂F : p₂ ∈ spPerp f F) (hp'F : p' ∈ spPerp f F)
    (hp₂'F : p₂' ∈ spPerp f F) (hp0 : p ≠ 0) (hp₂0 : p₂ ≠ 0) (hp'0 : p' ≠ 0)
    (hp₂'0 : p₂' ≠ 0) (hpp₂ : f p p₂ = 0) (hne : p₂ ≠ p) (hpp₂' : f p' p₂' = 0)
    (hne' : p₂' ≠ p') : ∃ g ∈ spRadGen f F, g p = p' ∧ g p₂ = p₂' := by
  obtain ⟨g₁, hg₁, hg₁p⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hpF hp'F hp0 hp'0
  have hg₁S := spRadGen_le_spFix F hg₁
  set x := g₁ p₂ with hx
  have hxF : x ∈ spPerp f F := apply_mem_spPerp hg₁S.1 hg₁S.2 hp₂F
  have hp'x : f p' x = 0 := by
    rw [hx, ← hg₁p, TauCeti.BilinForm.mem_isometryGroup_iff.mp hg₁S.1, hpp₂]
  have hxne : x ≠ p' := fun h => hne (g₁.injective (by rw [← hx, h, hg₁p]))
  obtain ⟨p₁', hp₁'F, hpp₁'⟩ := sp_exists_partner hf hnd hF hp'F hp'0
  set K := F ⊔ Submodule.span (ZMod 2) {p', p₁'} with hKdef
  have hK : K ⊓ spPerp f K = ⊥ := sup_span_pair_inf_spPerp_eq_bot hf hF hp'F hp₁'F hpp₁'
  have hcomp : ∀ y : V, y ∈ spPerp f F → f p' y = 0 → y ≠ 0 → y ≠ p' →
      y - f y p₁' • p' ∈ spPerp f K ∧ y - f y p₁' • p' ≠ 0 := by
    intro y hyF hp'y hy0 hyp'
    have h := sp_sub_mem_spPerp_sup_span_pair hf hp'F hp₁'F hpp₁' hyF
    have hyp'0 : f y p' = 0 := by rw [isAlt_symm hf, hp'y]
    rw [hyp'0, zero_smul, sub_zero] at h
    refine ⟨h, fun h0 => ?_⟩
    rw [sub_eq_zero] at h0
    rcases zmod2_eq_zero_or_eq_one (f y p₁') with hc | hc
    · rw [hc, zero_smul] at h0
      exact hy0 h0
    · rw [hc, one_smul] at h0
      exact hyp' h0
  obtain ⟨hsK, hs0⟩ := hcomp x hxF hp'x (fun h => hp₂0 (g₁.map_eq_zero_iff.mp h)) hxne
  obtain ⟨hs'K, hs'0⟩ := hcomp p₂' hp₂'F hpp₂' hp₂'0 hne'
  set c := f x p₁' with hc
  set c' := f p₂' p₁' with hc'
  obtain ⟨g₂, hg₂, hg₂s⟩ := exists_mem_spRadGen_apply_eq hf hnd hK hsK hs'K hs0 hs'0
  obtain ⟨-, hg₂p', -⟩ := mem_spFix_sup_span_pair.mp (spRadGen_le_spFix K hg₂)
  have hg₂x : g₂ x = (p₂' - c' • p') + c • p' := by
    have : x = (x - c • p') + c • p' := by abel
    rw [this, map_add, map_smul, hg₂s, hg₂p']
  have hg₂G : g₂ ∈ spRadGen f F := spRadGen_sup_span_pair_le hg₂
  by_cases hcc : c = c'
  · refine ⟨g₂ * g₁, mul_mem hg₂G hg₁, ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, hg₁p, hg₂p']
    · rw [LinearEquiv.mul_apply, ← hx, hg₂x, hcc, sub_add_cancel]
  · have hc1 : c' = c + 1 := by
      rcases zmod2_eq_zero_or_eq_one c with h | h <;>
        rcases zmod2_eq_zero_or_eq_one c' with h' | h'
      · exact absurd (h.trans h'.symm) hcc
      · rw [h, h']
        decide
      · rw [h, h']
        decide
      · exact absurd (h.trans h'.symm) hcc
    obtain ⟨u, huK, hus'⟩ := exists_mem_spPerp_apply_eq_one hf hnd hK hs'K hs'0
    obtain ⟨huF, hp'u, -⟩ := mem_spPerp_sup_span_pair.mp huK
    have hg₃ : spSiegel f hf p' u 0 ∈ spRadFix f F p' :=
      (mem_spRadFix_iff hf hnd hp'0 hp'F).mpr ⟨u, huF, hp'u, 0, rfl⟩
    have hs'p' : f (p₂' - c' • p') p' = 0 := by
      rw [isAlt_symm hf]
      exact (mem_spPerp_sup_span_pair.mp hs'K).2.1
    refine ⟨spSiegel f hf p' u 0 * g₂ * g₁, mul_mem (mul_mem (spRadFix_le_spRadGen hp'F hp'0 hg₃)
      hg₂G) hg₁, ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg₁p, hg₂p']
      exact hg₃.1.2.1
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hx, hg₂x, map_add, map_smul,
        hg₃.1.2.1, spSiegel_apply hf hp'u, hs'p', isAlt_symm hf, hus', zero_smul, add_zero,
        zero_mul, add_zero, one_smul, hc1, add_smul, one_smul]
      abel

theorem sp_timmesfeld_2_4 (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {φ : V →ₗ[ZMod 2] V} (hφ : ∀ x ∈ spPerp f F, φ x ∈ spPerp f F)
    (hcomm : ∀ g ∈ spFix f F, ∀ x ∈ spPerp f F, φ (g x) = g (φ x)) :
    ∃ c : ZMod 2, ∀ x ∈ spPerp f F, φ x = c • x := by
  by_cases hne : spPerp f F = ⊥
  · exact ⟨0, fun x hx => by
      rw [hne, Submodule.mem_bot] at hx
      rw [hx, map_zero, smul_zero]⟩
  obtain ⟨p₀, hp₀F, hp₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfix : φ p₀ ∈ (ZMod 2) ∙ p₀ := by
    refine sp_fixed_mem_span_of_spRadFix hf hnd hF hp₀F hp₀0 (hφ p₀ hp₀F) fun t ht => ?_
    rw [← hcomm t (spRadFix_le_spFix F p₀ ht) p₀ hp₀F, ht.1.2.1]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfix
  refine ⟨c, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, smul_zero]
  obtain ⟨g, hg, hgx⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hp₀F hx hp₀0 hx0
  rw [← hgx, hcomm g (spRadGen_le_spFix F hg) p₀ hp₀F, ← hc, map_smul]

theorem sp_timmesfeld_2_4_sp (hf : f.IsAlt) (hnd : f.Nondegenerate) {φ : V →ₗ[ZMod 2] V}
    (hcomm : ∀ g ∈ TauCeti.BilinForm.isometryGroup f, ∀ x, φ (g x) = g (φ x)) :
    ∃ c : ZMod 2, φ = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := sp_timmesfeld_2_4 hf hnd (bot_inf_eq _)
    (fun x _ => by rw [spPerp_bot]; exact Submodule.mem_top)
    (fun g hg x _ => hcomm g (by rw [spFix_bot] at hg; exact hg) x)
  exact ⟨c, LinearMap.ext fun x => by rw [hc x (by rw [spPerp_bot]; exact Submodule.mem_top)]; rfl⟩

end S2

end CFSG.LargeExtraspecial
