module

public import CFSG.LargeExtraspecial.S2OrthGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem sub_mem_perp_sup_span_pair {F : Submodule (ZMod 2) V} {p p₁ : V} (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hpp₁ : polar q p p₁ = 1) {x : V} (hx : x ∈ perp q F) :
    x - polar q x p₁ • p - polar q x p • p₁ ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) := by
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  refine mem_perp_sup_span_pair.mpr ⟨Submodule.sub_mem _ (Submodule.sub_mem _ hx
    (Submodule.smul_mem _ _ hpF)) (Submodule.smul_mem _ _ hp₁F), ?_, ?_⟩
  · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right,
      polar_self_eq_zero, hpp₁, polar_comm q p x]
    simp
  · rw [polar_sub_right, polar_sub_right, polar_smul_right, polar_smul_right, hp₁p,
      polar_self_eq_zero, polar_comm q p₁ x]
    simp

theorem fixed_mem_span_of_radFix (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {p : V}
    (hpF : p ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) {x : V} (hx : x ∈ perp q F)
    (hfix : ∀ t ∈ radFix q F p, t x = x) : x ∈ (ZMod 2) ∙ p := by
  obtain ⟨p₁, hp₁F, hp₁, hpp₁⟩ := exists_hyperbolic_partner hq hF hpF hp0 hp
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  have hE : ∀ u ∈ perp q K, eichler q p u x = x := fun u hu =>
    hfix _ ((mem_radFix_iff hq hp0 hp hpF).mpr ⟨u, perp_sup_span_pair_le hu,
      (mem_perp_sup_span_pair.mp hu).2.1, rfl⟩)
  have hxp : polar q x p = 0 := by
    have hne : perp q K ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hKdim
      omega
    obtain ⟨u, huK, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨-, hpu, hp₁u⟩ := mem_perp_sup_span_pair.mp huK
    have h := hE u huK
    rw [eichler_apply_zmod2 hp hpu, add_assoc, add_eq_left] at h
    by_contra hne'
    rw [zmod2_eq_one_of_ne_zero hne', one_smul] at h
    have hu : u = (polar q x u + q u * 1) • p := by
      rw [add_eq_zero_iff_eq_neg, vec_neg] at h
      exact h
    have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
    rw [hu, polar_smul_right, hp₁p, smul_eq_mul, mul_one] at hp₁u
    rw [hp₁u, zero_smul] at hu
    exact hu0 hu
  have hx0 := sub_mem_perp_sup_span_pair hpF hp₁F hpp₁ hx
  set x₀ := x - polar q x p₁ • p - polar q x p • p₁ with hx₀
  have hx₀0 : x₀ = 0 := by
    by_contra hne
    obtain ⟨y, hyK, hyx⟩ := exists_mem_perp_polar_eq_one hq hK hx0 hne
    obtain ⟨-, hpy, -⟩ := mem_perp_sup_span_pair.mp hyK
    have h := hE y hyK
    rw [eichler_apply_zmod2 hp hpy, hxp, zero_smul, add_zero, mul_zero, add_zero, add_eq_left,
      smul_eq_zero] at h
    rcases h with h | h
    · have : polar q x₀ y = polar q x y := by
        rw [hx₀, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hpy,
          (mem_perp_sup_span_pair.mp hyK).2.2]
        simp
      rw [polar_comm, this, h] at hyx
      exact zero_ne_one hyx
    · exact hp0 h
  have : x = polar q x p₁ • p := by
    rw [hx₀, hxp, zero_smul, sub_zero, sub_eq_zero] at hx₀0
    exact hx₀0
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)

theorem eq_of_radFix_eq (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {p p' : V}
    (hpF : p ∈ perp q F) (hp'F : p' ∈ perp q F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (hp : q p = 0)
    (h : radFix q F p = radFix q F p') : p = p' := by
  have hmem : p' ∈ (ZMod 2) ∙ p := by
    refine fixed_mem_span_of_radFix hq hF h4 hpF hp0 hp hp'F fun t ht => ?_
    rw [h] at ht
    exact ht.1.2.1
  rcases mem_span_singleton_iff.mp hmem with h0 | h1
  · exact absurd h0 hp'0
  · exact h1.symm

theorem mem_normalizer_radFix_iff (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {p : V}
    (hpF : p ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ omegaFix q hq F) :
    g ∈ Subgroup.normalizer (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ↔ g p = p := by
  have hgO := mem_orthogonalGroup_of_mem_omegaFix hg
  constructor
  · intro hN
    have hgpF : g p ∈ perp q F := apply_mem_perp hgO hg.2 hpF
    have hgp0 : g p ≠ 0 := fun h => hp0 (g.map_eq_zero_iff.mp h)
    have hgp : q (g p) = 0 := by
      rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO, hp]
    refine eq_of_radFix_eq hq hF h4 hgpF hpF hgp0 hp0 hgp ?_
    ext x
    rw [map_conj_radFix hq hp0 hp hpF hgO hg.2 x]
    rw [Subgroup.mem_normalizer_iff''] at hN
    exact (hN x).symm
  · intro hgp
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    have := map_conj_radFix hq hp0 hp hpF hgO hg.2 x
    rw [hgp] at this
    exact this

theorem timmesfeld_2_1_b1 (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m)
    {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) :
    (∀ g, g ∈ omegaFix q hq (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
      g ∈ omegaFix q hq F ∧ g ∈ Subgroup.normalizer (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ∧
        g ∈ Subgroup.normalizer (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V))) ∧
    (∀ g ∈ omegaFix q hq F, g ∈ Subgroup.normalizer (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) →
      ∃ t ∈ radFix q F p, ∃ y ∈ omegaFix q hq (F ⊔ Submodule.span (ZMod 2) {p, p₁}),
        g = t * y) ∧
    radFix q F p ⊓ omegaFix q hq (F ⊔ Submodule.span (ZMod 2) {p, p₁}) = ⊥ := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  refine ⟨fun g => ?_, fun g hg hN => ?_, radFix_inf_omegaFix_eq_bot hq hp0 hp hpp₁⟩
  · rw [mem_omegaFix_sup_span_pair]
    constructor
    · rintro ⟨hg, hgp, hgp₁⟩
      exact ⟨hg, (mem_normalizer_radFix_iff hq hF (by omega) hpF hp0 hp hg).mpr hgp,
        (mem_normalizer_radFix_iff hq hF (by omega) hp₁F hp₁0 hp₁ hg).mpr hgp₁⟩
    · rintro ⟨hg, hN, hN₁⟩
      exact ⟨hg, (mem_normalizer_radFix_iff hq hF (by omega) hpF hp0 hp hg).mp hN,
        (mem_normalizer_radFix_iff hq hF (by omega) hp₁F hp₁0 hp₁ hg).mp hN₁⟩
  · have hgp := (mem_normalizer_radFix_iff hq hF (by omega) hpF hp0 hp hg).mp hN
    obtain ⟨t, ht, hty⟩ := exists_mem_radFix_inv_mul_mem hq hpF hp₁F hp0 hp hp₁ hpp₁ hg hgp
    exact ⟨t, ht, t⁻¹ * g, hty, by group⟩

theorem radFix_inf_eq_bot_iff (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p p' : V} (hpF : p ∈ perp q F) (hp'F : p' ∈ perp q F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0)
    (hpp' : p ≠ p') (hp : q p = 0) (hp' : q p' = 0) :
    radFix q F p ⊓ radFix q F p' = ⊥ ↔ polar q p p' = 1 := by
  constructor
  · intro h
    by_contra hne
    have h0 : polar q p p' = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right hne
    have hli : LinearIndependent (ZMod 2) ![p, p'] :=
      linearIndependent_pair_iff.mpr ⟨hp0, hp'0, hpp'⟩
    have hmem : eichler q p p' ∈ radFix q F p ⊓ radFix q F p' := by
      obtain ⟨h1, h2⟩ := eichler_mem_pointRadical_inf hp hp' h0
      have hfix := eichler_mem_fixGroup (F := F) hpF hp'F
      exact ⟨⟨h1, hfix⟩, ⟨h2, hfix⟩⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact eichler_ne_one hq hp h0 hli hmem
  · intro h
    rw [eq_bot_iff]
    rintro t ⟨ht, ht'⟩
    have := pointRadical_inf_eq_bot hq hp0 hp h
    rw [eq_bot_iff] at this
    exact this ⟨ht.1, ht'.1⟩

theorem normalizer_inf_radFix_eq_bot (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {p p₁ : V}
    (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1) :
    radFix q F p ⊓ Subgroup.normalizer (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)) = ⊥ := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  rw [eq_bot_iff]
  rintro t ⟨ht, hN⟩
  have htΩ := radFix_le_omegaFix hq hp0 hp ht
  have htp₁ := (mem_normalizer_radFix_iff hq hF h4 hp₁F hp₁0 hp₁ htΩ).mp hN
  exact (Subgroup.mem_bot).mpr (eq_one_of_mem_pointRadical_of_apply_eq hq hp0 hp hpp₁ ht.1 htp₁)

theorem exists_mem_radGen_apply_eq_orth (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {m : ℕ} (hm : 3 ≤ m)
    (hdim : finrank (ZMod 2) (perp q F) = 2 * m) {p p₂ p' p₂' : V} (hpF : p ∈ perp q F)
    (hp₂F : p₂ ∈ perp q F) (hp'F : p' ∈ perp q F) (hp₂'F : p₂' ∈ perp q F) (hp0 : p ≠ 0)
    (hp₂0 : p₂ ≠ 0) (hp'0 : p' ≠ 0) (hp₂'0 : p₂' ≠ 0) (hp : q p = 0) (hp₂ : q p₂ = 0)
    (hp' : q p' = 0) (hp₂' : q p₂' = 0) (hpp₂ : polar q p p₂ = 0) (hne : p₂ ≠ p)
    (hpp₂' : polar q p' p₂' = 0) (hne' : p₂' ≠ p') :
    ∃ g ∈ radGen q F, g p = p' ∧ g p₂ = p₂' := by
  obtain ⟨g₁, hg₁, hg₁p⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hpF hp'F hp0 hp'0 hp hp'
  have hg₁Ω := radGen_le_omegaFix hq F hg₁
  have hg₁O := mem_orthogonalGroup_of_mem_omegaFix hg₁Ω
  set x := g₁ p₂ with hx
  have hxF : x ∈ perp q F := apply_mem_perp hg₁O hg₁Ω.2 hp₂F
  have hqx : q x = 0 := by rw [hx, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg₁O, hp₂]
  have hp'x : polar q p' x = 0 := by
    rw [hx, ← hg₁p, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg₁O, hpp₂]
  have hxne : x ≠ p' := fun h => hne (g₁.injective (by rw [← hx, h, hg₁p]))
  obtain ⟨p₁', hp₁'F, hp₁', hpp₁'⟩ := exists_hyperbolic_partner hq hF hp'F hp'0 hp'
  set K := F ⊔ Submodule.span (ZMod 2) {p', p₁'} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hp'F hp₁'F hpp₁'
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hp'F hp₁'F hpp₁'
  have hcomp : ∀ y : V, y ∈ perp q F → q y = 0 → polar q p' y = 0 → y ≠ 0 → y ≠ p' →
      y - polar q y p₁' • p' ∈ perp q K ∧ q (y - polar q y p₁' • p') = 0 ∧
        y - polar q y p₁' • p' ≠ 0 := by
    intro y hyF hy hp'y hy0 hyp'
    have h := sub_mem_perp_sup_span_pair hp'F hp₁'F hpp₁' hyF
    have hyp'0 : polar q y p' = 0 := by rw [polar_comm, hp'y]
    rw [hyp'0, zero_smul, sub_zero] at h
    refine ⟨h, ?_, ?_⟩
    · rw [vec_sub, map_add_eq, hy, map_smul_zmod2, hp', mul_zero, polar_smul_right, hyp'0,
        smul_zero]
      simp
    · intro h0
      rw [sub_eq_zero] at h0
      rcases zmod2_eq_zero_or_eq_one (polar q y p₁') with hc | hc
      · rw [hc, zero_smul] at h0
        exact hy0 h0
      · rw [hc, one_smul] at h0
        exact hyp' h0
  obtain ⟨hsK, hs, hs0⟩ :=
    hcomp x hxF hqx hp'x (fun h => hp₂0 (g₁.map_eq_zero_iff.mp h)) hxne
  obtain ⟨hs'K, hs', hs'0⟩ := hcomp p₂' hp₂'F hp₂' hpp₂' hp₂'0 hne'
  set c := polar q x p₁' with hc
  set c' := polar q p₂' p₁' with hc'
  obtain ⟨g₂, hg₂, hg₂s⟩ := exists_mem_radGen_apply_eq hq hK (by omega) hsK hs'K hs0 hs'0 hs hs'
  obtain ⟨hg₂F, hg₂p', -⟩ := mem_omegaFix_sup_span_pair.mp (radGen_le_omegaFix hq K hg₂)
  have hg₂x : g₂ x = (p₂' - c' • p') + c • p' := by
    have : x = (x - c • p') + c • p' := by abel
    rw [this, map_add, map_smul, hg₂s, hg₂p']
  have hg₂G : g₂ ∈ radGen q F := radGen_sup_span_pair_le hg₂
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
    obtain ⟨u, huK, hus'⟩ := exists_mem_perp_polar_eq_one hq hK hs'K hs'0
    obtain ⟨huF, hp'u, -⟩ := mem_perp_sup_span_pair.mp huK
    have hg₃ : eichler q p' u ∈ radFix q F p' :=
      (mem_radFix_iff hq hp'0 hp' hp'F).mpr ⟨u, huF, hp'u, rfl⟩
    have hs'p' : polar q (p₂' - c' • p') p' = 0 := by
      rw [polar_comm]
      exact (mem_perp_sup_span_pair.mp hs'K).2.1
    refine ⟨eichler q p' u * g₂ * g₁, mul_mem (mul_mem (radFix_le_radGen hp'F hp'0 hp' hg₃)
      hg₂G) hg₁, ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg₁p, hg₂p',
        CFSG.ClassicalGroups.Orthogonal.eichler_apply_self]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hx, hg₂x, map_add, map_smul,
        CFSG.ClassicalGroups.Orthogonal.eichler_apply_self, eichler_apply_zmod2 hp' hp'u,
        hs'p', polar_comm, hus', zero_smul, add_zero, mul_zero, add_zero, one_smul, hc1,
        add_smul, one_smul]
      abel

theorem timmesfeld_2_4_omega (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h4 : 4 ≤ finrank (ZMod 2) (perp q F)) {φ : V →ₗ[ZMod 2] V}
    (hφ : ∀ x ∈ perp q F, φ x ∈ perp q F)
    (hcomm : ∀ g ∈ omegaFix q hq F, ∀ x ∈ perp q F, φ (g x) = g (φ x)) :
    ∃ c : ZMod 2, ∀ x ∈ perp q F, φ x = c • x := by
  obtain ⟨p₀, hp₀F, hp₀0, hp₀⟩ := exists_singular_mem_perp (q := q) (F := F) (by omega)
  have hfix : ∀ p ∈ perp q F, p ≠ 0 → q p = 0 → φ p ∈ (ZMod 2) ∙ p := by
    intro p hpF hp0 hp
    refine fixed_mem_span_of_radFix hq hF h4 hpF hp0 hp (hφ p hpF) fun t ht => ?_
    rw [← hcomm t (radFix_le_omegaFix hq hp0 hp ht) p hpF, ht.1.2.1]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hfix p₀ hp₀F hp₀0 hp₀)
  refine ⟨c, ?_⟩
  have hsing : ∀ s ∈ perp q F, q s = 0 → φ s = c • s := by
    intro s hsF hs
    by_cases hs0 : s = 0
    · rw [hs0, map_zero, smul_zero]
    obtain ⟨g, hg, hgs⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hp₀F hsF hp₀0 hs0 hp₀ hs
    rw [← hgs, hcomm g (radGen_le_omegaFix hq F hg) p₀ hp₀F, ← hc, map_smul]
  obtain ⟨p₁, hp₁F, hp₁, hpp₁⟩ := exists_hyperbolic_partner hq hF hp₀F hp₀0 hp₀
  intro x hx
  have hx₀ := sub_mem_perp_sup_span_pair hp₀F hp₁F hpp₁ hx
  set x₀ := x - polar q x p₁ • p₀ - polar q x p₀ • p₁ with hx₀def
  obtain ⟨hx₀F, hp₀x₀, hp₁x₀⟩ := mem_perp_sup_span_pair.mp hx₀
  have hφx₀ : φ x₀ = c • x₀ := by
    rcases zmod2_eq_zero_or_eq_one (q x₀) with h | h
    · exact hsing x₀ hx₀F h
    · have hs : q (x₀ + p₀ + p₁) = 0 := by
        rw [map_add_eq, map_add_eq, h, hp₀, hp₁, polar_add_left, polar_comm, hp₀x₀,
          polar_comm q x₀ p₁, hp₁x₀, hpp₁]
        decide
      have h1 := hsing _ (Submodule.add_mem _ (Submodule.add_mem _ hx₀F hp₀F) hp₁F) hs
      rw [map_add, map_add, hsing p₀ hp₀F hp₀, hsing p₁ hp₁F hp₁, smul_add, smul_add] at h1
      exact add_right_cancel (add_right_cancel h1)
  have hx' : x = x₀ + polar q x p₁ • p₀ + polar q x p₀ • p₁ := by
    rw [hx₀def]
    abel
  rw [hx', map_add, map_add, map_smul, map_smul, hφx₀, hsing p₀ hp₀F hp₀, hsing p₁ hp₁F hp₁,
    smul_add, smul_add, smul_comm c (polar q x p₁), smul_comm c (polar q x p₀)]

theorem timmesfeld_2_4_omegaGroup (hq : q.polarBilin.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V) {φ : V →ₗ[ZMod 2] V}
    (hcomm : ∀ g ∈ omegaGroup q hq, ∀ x, φ (g x) = g (φ x)) :
    ∃ c : ZMod 2, φ = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := timmesfeld_2_4_omega hq (bot_inf_eq _) (by rw [perp_bot, finrank_top]; exact h4)
    (fun x _ => by rw [perp_bot]; exact Submodule.mem_top)
    (fun g hg x _ => hcomm g (by rw [omegaFix_bot] at hg; exact hg) x)
  exact ⟨c, LinearMap.ext fun x => by rw [hc x (by rw [perp_bot]; exact Submodule.mem_top)]; rfl⟩

end S2

end CFSG.LargeExtraspecial
