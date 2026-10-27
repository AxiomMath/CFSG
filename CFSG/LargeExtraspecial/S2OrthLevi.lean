module

public import CFSG.LargeExtraspecial.S2OrthGeom

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
theorem mem_perp_sup {F T : Submodule (ZMod 2) V} {x : V} :
    x ∈ perp q (F ⊔ T) ↔ x ∈ perp q F ∧ x ∈ perp q T := by
  simp only [mem_perp]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Submodule.mem_sup_left hy),
      fun y hy => h y (Submodule.mem_sup_right hy)⟩
  · rintro ⟨hF, hT⟩ y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_left, hF a ha, hT b hb, add_zero]

theorem two_mul_finrank_le_of_polar_eq_zero (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {T : Submodule (ZMod 2) V}
    (hT : T ≤ perp q F) (hiso : ∀ x ∈ T, ∀ y ∈ T, polar q x y = 0) :
    2 * finrank (ZMod 2) T ≤ finrank (ZMod 2) (perp q F) := by
  have hle : T ≤ perp q (F ⊔ T) := fun x hx =>
    mem_perp_sup.mpr ⟨hT hx, mem_perp.mpr fun y hy => hiso y hy x hx⟩
  have hinf : F ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← hF]
    exact inf_le_inf_left _ hT
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq F T
  rw [hinf, finrank_bot, add_zero] at h2
  rw [LinearMap.BilinForm.finrank_orthogonal hq] at h1 ⊢
  have h3 := Submodule.finrank_le (F ⊔ T)
  omega

theorem exists_mem_map_eq_one_of_lt (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {T : Submodule (ZMod 2) V}
    (hT : T ≤ perp q F) (hlt : finrank (ZMod 2) (perp q F) < 2 * finrank (ZMod 2) T) :
    ∃ x ∈ T, q x = 1 := by
  by_contra! h
  have h0 : ∀ x ∈ T, q x = 0 := fun x hx => (zmod2_eq_zero_or_eq_one _).resolve_right (h x hx)
  have hiso : ∀ x ∈ T, ∀ y ∈ T, polar q x y = 0 := by
    intro x hx y hy
    have := h0 (x + y) (T.add_mem hx hy)
    rw [map_add_eq, h0 x hx, h0 y hy, zero_add, zero_add] at this
    exact this
  have := two_mul_finrank_le_of_polar_eq_zero hq hF hT hiso
  omega

theorem finrank_perp_sup_span_singleton_add_one (hq : q.polarBilin.Nondegenerate)
    (F : Submodule (ZMod 2) V) (x : V) :
    finrank (ZMod 2) (perp q F) ≤ finrank (ZMod 2) (perp q (F ⊔ (ZMod 2) ∙ x)) + 1 := by
  rw [LinearMap.BilinForm.finrank_orthogonal hq, LinearMap.BilinForm.finrank_orthogonal hq]
  have h1 := Submodule.finrank_add_le_finrank_add_finrank F ((ZMod 2) ∙ x)
  have h2 : finrank (ZMod 2) ((ZMod 2) ∙ x) ≤ 1 := by
    simpa using finrank_span_le_card ({x} : Set V)
  have h3 := Submodule.finrank_le F
  have h4 := Submodule.finrank_le (F ⊔ (ZMod 2) ∙ x)
  omega

theorem exists_common_nonorth (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {p p' : V}
    (hpF : p ∈ perp q F) (hp'F : p' ∈ perp q F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (hp : q p = 0)
    (hp' : q p' = 0) :
    ∃ p'' ∈ perp q F, q p'' = 0 ∧ polar q p'' p = 1 ∧ polar q p'' p' = 1 := by
  rcases zmod2_eq_zero_or_eq_one (polar q p p') with h0 | h1
  ·
    obtain ⟨x, hxF, hxp, hxp'⟩ : ∃ x ∈ perp q F, polar q x p = 1 ∧ polar q x p' = 1 := by
      by_cases hpp' : p = p'
      · subst hpp'
        obtain ⟨x, hxF, hx⟩ := exists_mem_perp_polar_eq_one hq hF hpF hp0
        exact ⟨x, hxF, hx, hx⟩
      · exact exists_mem_perp_polar_eq_one_polar_eq_one hq hF hpF hp'F
          (linearIndependent_pair_iff.mpr ⟨hp0, hp'0, hpp'⟩)
    refine ⟨x + q x • p, Submodule.add_mem _ hxF (Submodule.smul_mem _ _ hpF), ?_, ?_, ?_⟩
    · rw [map_add_eq, map_smul_zmod2, hp, mul_zero, add_zero, polar_smul_right, hxp,
        smul_eq_mul, mul_one, zmod2_add_self]
    · rw [polar_add_left, polar_smul_left, polar_self_eq_zero, smul_zero, add_zero, hxp]
    · rw [polar_add_left, polar_smul_left, h0, smul_zero, add_zero, hxp']
  ·
    have hK := sup_span_pair_inf_perp_eq_bot hF hpF hp'F h1
    have hdim := finrank_perp_sup_span_pair hq hF hpF hp'F h1
    have hne : perp q (F ⊔ Submodule.span (ZMod 2) {p, p'}) ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim
      omega
    obtain ⟨w, hwK, hw⟩ := exists_mem_perp_map_eq_one hq hK hne
    obtain ⟨hwF, hpw, hp'w⟩ := mem_perp_sup_span_pair.mp hwK
    have hp'p : polar q p' p = 1 := by rw [polar_comm, h1]
    refine ⟨p + p' + w, Submodule.add_mem _ (Submodule.add_mem _ hpF hp'F) hwF, ?_, ?_, ?_⟩
    · rw [map_add_eq, map_add_eq, hp, hp', hw, h1, polar_add_left, hpw, hp'w]
      decide
    · rw [polar_add_left, polar_add_left, polar_self_eq_zero, hp'p, polar_comm, hpw]
      decide
    · rw [polar_add_left, polar_add_left, polar_self_eq_zero, h1, polar_comm, hp'w]
      decide

variable (q) in
@[expose] def radGen (F : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  Subgroup.closure {t | ∃ p ∈ perp q F, p ≠ 0 ∧ q p = 0 ∧ t ∈ radFix q F p}

omit [FiniteDimensional (ZMod 2) V] in
theorem radFix_le_radGen {F : Submodule (ZMod 2) V} {p : V} (hpF : p ∈ perp q F) (hp0 : p ≠ 0)
    (hp : q p = 0) : radFix q F p ≤ radGen q F :=
  fun _ ht => Subgroup.subset_closure ⟨p, hpF, hp0, hp, ht⟩

theorem radGen_le_omegaFix (hq : q.polarBilin.Nondegenerate) (F : Submodule (ZMod 2) V) :
    radGen q F ≤ omegaFix q hq F := by
  rw [radGen, Subgroup.closure_le]
  rintro t ⟨p, -, hp0, hp, ht⟩
  exact radFix_le_omegaFix hq hp0 hp ht

omit [FiniteDimensional (ZMod 2) V] in
theorem radGen_sup_span_pair_le {F : Submodule (ZMod 2) V} {p p₁ : V} :
    radGen q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ≤ radGen q F := by
  rw [radGen, Subgroup.closure_le]
  rintro t ⟨p', hp'K, hp'0, hp', ht⟩
  exact radFix_le_radGen (perp_sup_span_pair_le hp'K) hp'0 hp' (radFix_anti le_sup_left p' ht)

theorem exists_mem_radGen_apply_eq (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {p p' : V}
    (hpF : p ∈ perp q F) (hp'F : p' ∈ perp q F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (hp : q p = 0)
    (hp' : q p' = 0) : ∃ g ∈ radGen q F, g p = p' := by
  obtain ⟨p'', hp''F, hp'', hp''p, hp''p'⟩ :=
    exists_common_nonorth hq hF h3 hpF hp'F hp0 hp'0 hp hp'
  have hp''0 : p'' ≠ 0 := by
    rintro rfl
    rw [polar_zero_left] at hp''p
    exact zero_ne_one hp''p
  obtain ⟨t, ht, htp⟩ := exists_mem_radFix_apply_eq hq hp''0 hp'' hp''F hpF hp'F hp hp' hp''p
    hp''p'
  exact ⟨t, radFix_le_radGen hp''F hp''0 hp'' ht, htp⟩

theorem exists_mem_radGen_apply_eq_pair (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F))
    {p p₁ p' p₁' : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp'F : p' ∈ perp q F)
    (hp₁'F : p₁' ∈ perp q F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hp' : q p' = 0) (hp₁' : q p₁' = 0) (hpp₁ : polar q p p₁ = 1)
    (hpp₁' : polar q p' p₁' = 1) :
    ∃ g ∈ radGen q F, g p = p' ∧ g p₁ = p₁' := by
  obtain ⟨g, hg, hgp⟩ := exists_mem_radGen_apply_eq hq hF h3 hpF hp'F hp0 hp'0 hp hp'
  have hgO := mem_orthogonalGroup_of_mem_omegaFix (radGen_le_omegaFix hq F hg)
  have hgF := (radGen_le_omegaFix hq F hg).2
  have hgp₁F : g p₁ ∈ perp q F := apply_mem_perp hgO hgF hp₁F
  have hgp₁ : q (g p₁) = 0 := by rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO, hp₁]
  have hp'gp₁ : polar q p' (g p₁) = 1 := by
    rw [← hgp, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO, hpp₁]
  obtain ⟨t, ht, htp⟩ := exists_mem_radFix_apply_eq hq hp'0 hp' hp'F hgp₁F hp₁'F hgp₁ hp₁'
    hp'gp₁ hpp₁'
  refine ⟨t * g, mul_mem (radFix_le_radGen hp'F hp'0 hp' ht) hg, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hgp]
    exact ht.1.2.1
  · rw [LinearEquiv.mul_apply, htp]

theorem exists_mem_radFix_inv_mul_mem (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ omegaFix q hq F) (hgp : g p = p) :
    ∃ t ∈ radFix q F p, t⁻¹ * g ∈ omegaFix q hq (F ⊔ Submodule.span (ZMod 2) {p, p₁}) := by
  have hgO := mem_orthogonalGroup_of_mem_omegaFix hg
  have hgp₁F : g p₁ ∈ perp q F := apply_mem_perp hgO hg.2 hp₁F
  have hgp₁ : q (g p₁) = 0 := by rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO, hp₁]
  have hpgp₁ : polar q p (g p₁) = 1 := by
    rw [← hgp, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO, hpp₁]
  obtain ⟨t, ht, htp₁⟩ := exists_mem_radFix_apply_eq hq hp0 hp hpF hp₁F hgp₁F hp₁ hgp₁ hpp₁ hpgp₁
  have htΩ := radFix_le_omegaFix hq hp0 hp ht
  refine ⟨t, ht, mem_omegaFix_sup_span_pair.mpr ⟨mul_mem (inv_mem htΩ) hg, ?_, ?_⟩⟩
  · rw [LinearEquiv.mul_apply, hgp]
    conv_lhs => rw [← ht.1.2.1]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' t p
  · rw [LinearEquiv.mul_apply, ← htp₁]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' t p₁

theorem radFix_inf_omegaFix_eq_bot (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) :
    radFix q F p ⊓ omegaFix q hq (F ⊔ Submodule.span (ZMod 2) {p, p₁}) = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨ht, hty⟩
  exact (Subgroup.mem_bot).mpr (eq_one_of_mem_pointRadical_of_apply_eq hq hp0 hp hpp₁ ht.1
    (mem_omegaFix_sup_span_pair.mp hty).2.2)

theorem exists_eq_eichler_of_not_isTypeA (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p : V} (hpF : p ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ radFix q F p) (ht1 : t ≠ 1) (hta : ¬ IsTypeA q t 2) :
    ∃ u ∈ perp q F, polar q p u = 0 ∧ q u = 1 ∧ t = eichler q p u := by
  obtain ⟨u, huF, hpu, rfl⟩ := (mem_radFix_iff hq hp0 hp hpF).mp ht
  refine ⟨u, huF, hpu, ?_, rfl⟩
  rcases zmod2_eq_zero_or_eq_one (q u) with hu | hu
  · exfalso
    have hun : u ∉ (ZMod 2) ∙ p := fun h => ht1 ((eichler_eq_one_iff hq hp0 hp hpu).mpr h)
    have hli : LinearIndependent (ZMod 2) ![p, u] := by
      refine linearIndependent_pair_iff.mpr ⟨hp0, fun h => hun (h ▸ Submodule.zero_mem _),
        fun h => hun (h ▸ Submodule.mem_span_singleton_self p)⟩
    exact hta (eichler_isTypeA hq hp hpu hli hu).1
  · exact hu

theorem not_isTypeA_eichler (hq : q.polarBilin.Nondegenerate) {p u : V} (hp0 : p ≠ 0)
    (hp : q p = 0) (hpu : polar q p u = 0) (hu : q u = 1) : ¬ IsTypeA q (eichler q p u) 2 := by
  intro hA
  obtain ⟨hC, -⟩ := eichler_isTypeC hq hp0 hp hpu hu
  obtain ⟨-, -, -, -, -, x, hx, hqx⟩ := hC
  exact hqx (hA.2.2.2.2 x hx)

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_eichler_apply_self {p p₁ u : V} (hp₁ : q p₁ = 0) (hp₁u : polar q p₁ u = 0)
    (hu : q u = 1) (hpp₁ : polar q p p₁ = 1) : polar q (eichler q p₁ u p) p = 1 := by
  rw [eichler_apply_zmod2 hp₁ hp₁u, hpp₁, hu, one_smul, mul_one, polar_add_left, polar_add_left,
    polar_self_eq_zero, polar_smul_left, polar_comm q p₁ p, hpp₁, smul_eq_mul, mul_one,
    polar_comm q u p]
  rcases zmod2_eq_zero_or_eq_one (polar q p u) with h | h <;> rw [h] <;> decide

theorem polar_apply_eq_one_of_not_isTypeA (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p p₁ : V} (hp₁F : p₁ ∈ perp q F) (hp₁0 : p₁ ≠ 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ radFix q F p₁)
    (hx1 : x ≠ 1) (hxa : ¬ IsTypeA q x 2) : polar q (x p) p = 1 := by
  obtain ⟨u, -, hp₁u, hu, rfl⟩ := exists_eq_eichler_of_not_isTypeA hq hp₁F hp₁0 hp₁ hx hx1 hxa
  exact polar_eichler_apply_self hp₁ hp₁u hu hpp₁

theorem exists_mem_radFix_not_isTypeA (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F))
    {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0)
    (hpp₁ : polar q p p₁ = 1) :
    ∃ c ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}), q c = 1 ∧
      eichler q p c ∈ radFix q F p ∧ eichler q p c ≠ 1 ∧ ¬ IsTypeA q (eichler q p c) 2 := by
  have hK := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hdim := finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  have hne : perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    omega
  obtain ⟨c, hcK, hc⟩ := exists_mem_perp_map_eq_one hq hK hne
  obtain ⟨hcF, hpc, -⟩ := mem_perp_sup_span_pair.mp hcK
  refine ⟨c, hcK, hc, (mem_radFix_iff hq hp0 hp hpF).mpr ⟨c, hcF, hpc, rfl⟩, ?_,
    not_isTypeA_eichler hq hp0 hp hpc hc⟩
  intro h1
  have hmem := (eichler_eq_one_iff hq hp0 hp hpc).mp h1
  rcases mem_span_singleton_iff.mp hmem with h | h
  · rw [h, map_zero] at hc
    exact zero_ne_one hc
  · rw [h, hp] at hc
    exact zero_ne_one hc

end S2

end CFSG.LargeExtraspecial
