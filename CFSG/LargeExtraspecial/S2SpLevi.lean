module

public import CFSG.LargeExtraspecial.S2SpRad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

theorem sp_exists_common_nonorth (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p p' : V} (hpF : p ∈ spPerp f F)
    (hp'F : p' ∈ spPerp f F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) :
    ∃ p'' ∈ spPerp f F, f p'' p = 1 ∧ f p'' p' = 1 := by
  by_cases hpp' : p = p'
  · subst hpp'
    obtain ⟨x, hxF, hx⟩ := exists_mem_spPerp_apply_eq_one hf hnd hF hpF hp0
    exact ⟨x, hxF, hx, hx⟩
  rcases zmod2_eq_zero_or_eq_one (f p p') with h0 | h1
  · exact exists_mem_spPerp_eq_one_eq_one hf hnd hF hpF hp'F
      (linearIndependent_pair_iff.mpr ⟨hp0, hp'0, hpp'⟩)
  · refine ⟨p + p', Submodule.add_mem _ hpF hp'F, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, hf.self_eq_zero, isAlt_symm hf, h1, zero_add]
    · rw [map_add, LinearMap.add_apply, hf.self_eq_zero, h1, add_zero]

variable (f) in
@[expose] def spRadGen (F : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  Subgroup.closure {t | ∃ p ∈ spPerp f F, p ≠ 0 ∧ t ∈ spRadFix f F p}

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadFix_le_spRadGen {F : Submodule (ZMod 2) V} {p : V} (hpF : p ∈ spPerp f F)
    (hp0 : p ≠ 0) : spRadFix f F p ≤ spRadGen f F :=
  fun _ ht => Subgroup.subset_closure ⟨p, hpF, hp0, ht⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadGen_le_spFix (F : Submodule (ZMod 2) V) : spRadGen f F ≤ spFix f F := by
  rw [spRadGen, Subgroup.closure_le]
  rintro t ⟨p, -, -, ht⟩
  exact spRadFix_le_spFix F p ht

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadGen_sup_span_pair_le {F : Submodule (ZMod 2) V} {p p₁ : V} :
    spRadGen f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ≤ spRadGen f F := by
  rw [spRadGen, Subgroup.closure_le]
  rintro t ⟨p', hp'K, hp'0, ht⟩
  exact spRadFix_le_spRadGen (spPerp_sup_span_pair_le hp'K) hp'0 (spRadFix_anti le_sup_left p' ht)

theorem exists_mem_spRadGen_apply_eq (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p p' : V} (hpF : p ∈ spPerp f F)
    (hp'F : p' ∈ spPerp f F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) : ∃ g ∈ spRadGen f F, g p = p' := by
  obtain ⟨p'', hp''F, hp''p, hp''p'⟩ := sp_exists_common_nonorth hf hnd hF hpF hp'F hp0 hp'0
  have hp''0 : p'' ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at hp''p
    exact zero_ne_one hp''p
  obtain ⟨t, ht, htp⟩ := exists_mem_spRadFix_apply_eq hf hp''F hpF hp'F hp''p hp''p'
  exact ⟨t, spRadFix_le_spRadGen hp''F hp''0 ht, htp⟩

theorem exists_mem_spRadGen_apply_eq_pair (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {p p₁ p' p₁' : V}
    (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hp'F : p' ∈ spPerp f F)
    (hp₁'F : p₁' ∈ spPerp f F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0) (hpp₁ : f p p₁ = 1)
    (hpp₁' : f p' p₁' = 1) : ∃ g ∈ spRadGen f F, g p = p' ∧ g p₁ = p₁' := by
  obtain ⟨g, hg, hgp⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hpF hp'F hp0 hp'0
  have hgS := spRadGen_le_spFix F hg
  have hgp₁F : g p₁ ∈ spPerp f F := apply_mem_spPerp hgS.1 hgS.2 hp₁F
  have hp'gp₁ : f p' (g p₁) = 1 := by
    rw [← hgp, TauCeti.BilinForm.mem_isometryGroup_iff.mp hgS.1, hpp₁]
  obtain ⟨t, ht, htp⟩ := exists_mem_spRadFix_apply_eq hf hp'F hgp₁F hp₁'F hp'gp₁ hpp₁'
  refine ⟨t * g, mul_mem (spRadFix_le_spRadGen hp'F hp'0 ht) hg, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hgp]
    exact ht.1.2.1
  · rw [LinearEquiv.mul_apply, htp]

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_mem_spRadFix_inv_mul_mem (hf : f.IsAlt) {F : Submodule (ZMod 2) V} {p p₁ : V}
    (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ spFix f F) (hgp : g p = p) :
    ∃ t ∈ spRadFix f F p, t⁻¹ * g ∈ spFix f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) := by
  have hgp₁F : g p₁ ∈ spPerp f F := apply_mem_spPerp hg.1 hg.2 hp₁F
  have hpgp₁ : f p (g p₁) = 1 := by
    rw [← hgp, TauCeti.BilinForm.mem_isometryGroup_iff.mp hg.1, hpp₁]
  obtain ⟨t, ht, htp₁⟩ := exists_mem_spRadFix_apply_eq hf hpF hp₁F hgp₁F hpp₁ hpgp₁
  have htS := spRadFix_le_spFix F p ht
  refine ⟨t, ht, mem_spFix_sup_span_pair.mpr ⟨mul_mem (inv_mem htS) hg, ?_, ?_⟩⟩
  · rw [LinearEquiv.mul_apply, hgp]
    conv_lhs => rw [← ht.1.2.1]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' t p
  · rw [LinearEquiv.mul_apply, ← htp₁]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' t p₁

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadFix_inf_spFix_eq_bot {F : Submodule (ZMod 2) V} {p p₁ : V} (hpp₁ : f p p₁ = 1) :
    spRadFix f F p ⊓ spFix f (F ⊔ Submodule.span (ZMod 2) {p, p₁}) = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨ht, hty⟩
  exact (Subgroup.mem_bot).mpr (eq_one_of_mem_spPointRadical_of_apply_eq hpp₁ ht.1
    (mem_spFix_sup_span_pair.mp hty).2.2)

theorem sp_exists_partner (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {p : V} (hpF : p ∈ spPerp f F) (hp0 : p ≠ 0) :
    ∃ p₁ ∈ spPerp f F, f p p₁ = 1 := by
  obtain ⟨y, hyF, hyp⟩ := exists_mem_spPerp_apply_eq_one hf hnd hF hpF hp0
  exact ⟨y, hyF, by rw [isAlt_symm hf, hyp]⟩

theorem spFix_le_spRadGen (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    ∀ (m : ℕ) (F : Submodule (ZMod 2) V), F ⊓ spPerp f F = ⊥ →
      finrank (ZMod 2) (spPerp f F) = 2 * m → spFix f F ≤ spRadGen f F := by
  intro m
  induction m with
  | zero =>
    intro F hF hdim g hg
    have htop : F ⊔ spPerp f F = ⊤ :=
      ((LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hf.isRefl).mpr
        (disjoint_iff.mpr hF)).sup_eq_top
    have hbot : spPerp f F = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    rw [hbot, sup_bot_eq] at htop
    have : g = 1 := LinearEquiv.ext fun x => hg.2 x (by rw [htop]; exact Submodule.mem_top)
    rw [this]
    exact one_mem _
  | succ m ih =>
    intro F hF hdim g hg
    have hne : spPerp f F ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hdim
      omega
    obtain ⟨p, hpF, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨p₁, hp₁F, hpp₁⟩ := sp_exists_partner hf hnd hF hpF hp0
    have hgpF : g p ∈ spPerp f F := apply_mem_spPerp hg.1 hg.2 hpF
    have hgp0 : g p ≠ 0 := fun h => hp0 (g.map_eq_zero_iff.mp h)
    obtain ⟨e, he, hep⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hgpF hpF hgp0 hp0
    have heg : e * g ∈ spFix f F := mul_mem (spRadGen_le_spFix F he) hg
    obtain ⟨t, ht, hty⟩ := exists_mem_spRadFix_inv_mul_mem hf hpF hp₁F hpp₁ heg
      (by rw [LinearEquiv.mul_apply, hep])
    have hK := sup_span_pair_inf_spPerp_eq_bot hf hF hpF hp₁F hpp₁
    have hKdim := finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
    have hy : t⁻¹ * (e * g) ∈ spRadGen f F :=
      spRadGen_sup_span_pair_le (ih _ hK (by omega) hty)
    have e1 : g = e⁻¹ * t * (t⁻¹ * (e * g)) := by group
    rw [e1]
    exact mul_mem (mul_mem (inv_mem he) (spRadFix_le_spRadGen hpF hp0 ht)) hy

theorem spRadFix_le_closure (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {p p₁ p' : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F)
    (hp'F : p' ∈ spPerp f F) (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0) (hp'0 : p' ≠ 0)
    (hpp₁ : f p p₁ = 1) :
    spRadFix f F p' ≤
      Subgroup.closure ((spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ∪ spRadFix f F p₁) := by
  set G₀ := Subgroup.closure ((spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ∪ spRadFix f F p₁)
  have hconj : ∀ {a b : V} {t : V ≃ₗ[ZMod 2] V}, a ∈ spPerp f F → a ≠ 0 →
      t ∈ G₀ → t ∈ spPointRadical f b ⊓ fixGroup F → spRadFix f F a ≤ G₀ →
      spRadFix f F (t a) ≤ G₀ := by
    intro a b t haF ha0 htG ht hL s hs
    have h := (map_conj_spRadFix hf hnd ha0 haF ht.1.1 ht.2 s).mp hs
    rw [show s = t * (t⁻¹ * s * t) * t⁻¹ by group]
    exact mul_mem (mul_mem htG (hL h)) (inv_mem htG)
  have key : ∀ {p'' : V}, p'' ∈ spPerp f F → p'' ≠ 0 → f p p'' = 1 →
      spRadFix f F p'' ≤ G₀ := by
    intro p'' hp''F hp''0 hpp''
    obtain ⟨t, ht, htp⟩ := exists_mem_spRadFix_apply_eq hf hpF hp₁F hp''F hpp₁ hpp''
    rw [← htp]
    exact hconj hp₁F hp₁0 (Subgroup.subset_closure (Or.inl ht)) ht
      (fun s hs => Subgroup.subset_closure (Or.inr hs))
  rcases zmod2_eq_zero_or_eq_one (f p p') with h0 | h1
  · obtain ⟨p'', hp''F, hp''p, hp''p'⟩ := sp_exists_common_nonorth hf hnd hF hpF hp'F hp0 hp'0
    have hp''0 : p'' ≠ 0 := by
      rintro rfl
      rw [map_zero, LinearMap.zero_apply] at hp''p
      exact zero_ne_one hp''p
    have hL'' := key hp''F hp''0 (by rw [isAlt_symm hf]; exact hp''p)
    obtain ⟨t, ht, htp⟩ := exists_mem_spRadFix_apply_eq hf hp''F hpF hp'F hp''p hp''p'
    rw [← htp]
    exact hconj hpF hp0 (hL'' ht) ht (fun s hs => Subgroup.subset_closure (Or.inl hs))
  · exact key hp'F hp'0 h1

theorem spFix_eq_closure_spRadFix (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {m : ℕ}
    (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m) {p p₁ : V} (hpF : p ∈ spPerp f F)
    (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) :
    spFix f F = Subgroup.closure ((spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ∪ spRadFix f F p₁) := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  refine le_antisymm ((spFix_le_spRadGen hf hnd m F hF hdim).trans ?_) ?_
  · rw [spRadGen, Subgroup.closure_le]
    rintro t ⟨p', hp'F, hp'0, ht⟩
    exact spRadFix_le_closure hf hnd hF hpF hp₁F hp'F hp0 hp₁0 hp'0 hpp₁ ht
  · rw [Subgroup.closure_le]
    rintro t (ht | ht)
    · exact spRadFix_le_spFix F p ht
    · exact spRadFix_le_spFix F p₁ ht

theorem exists_eq_spSiegel_one_of_not_isSpTypeA (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} {p : V} (hpF : p ∈ spPerp f F) (hp0 : p ≠ 0)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ spRadFix f F p) (ht1 : t ≠ 1) (hta : ¬ IsSpTypeA f t 2) :
    ∃ u ∈ spPerp f F, f p u = 0 ∧ t = spSiegel f hf p u 1 := by
  obtain ⟨u, huF, hpu, c, rfl⟩ := (mem_spRadFix_iff hf hnd hp0 hpF).mp ht
  refine ⟨u, huF, hpu, ?_⟩
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · exfalso
    have hun : u ∉ (ZMod 2) ∙ p := fun h =>
      ht1 ((spSiegel_eq_one_iff hf hnd hp0 hpu 0).mpr ⟨h, rfl⟩)
    have hli : LinearIndependent (ZMod 2) ![p, u] := by
      refine linearIndependent_pair_iff.mpr ⟨hp0, fun h => hun (h ▸ Submodule.zero_mem _),
        fun h => hun (h ▸ Submodule.mem_span_singleton_self p)⟩
    exact hta (isSpTypeA_spSiegel_zero hf hnd hpu hli)
  · rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_spSiegel_one_apply_self (hf : f.IsAlt) {p p₁ u : V} (hp₁u : f p₁ u = 0)
    (hpp₁ : f p p₁ = 1) : f (spSiegel f hf p₁ u 1 p) p = 1 := by
  have key : ∀ a : ZMod 2, a + (a + 1) = 1 := by decide
  rw [spSiegel_apply hf hp₁u, hpp₁, one_smul, one_mul]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hf.self_eq_zero,
    smul_eq_mul, zero_add]
  rw [isAlt_symm hf p₁ p, hpp₁, mul_one, isAlt_symm hf u p]
  exact key _

theorem spFix_eq_closure_insert (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {m : ℕ}
    (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m) {p p₁ : V} (hpF : p ∈ spPerp f F)
    (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) {x : V ≃ₗ[ZMod 2] V}
    (hx : x ∈ spRadFix f F p₁) (hx1 : x ≠ 1) (hxa : ¬ IsSpTypeA f x 2) :
    spFix f F = Subgroup.closure (insert x (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hxS := spRadFix_le_spFix F p₁ hx
  have hxpF : x p ∈ spPerp f F := apply_mem_spPerp hxS.1 hxS.2 hpF
  have hpxp : f p (x p) = 1 := by
    obtain ⟨u, -, hp₁u, rfl⟩ := exists_eq_spSiegel_one_of_not_isSpTypeA hf hnd hp₁F hp₁0 hx hx1 hxa
    rw [isAlt_symm hf]
    exact apply_spSiegel_one_apply_self hf hp₁u hpp₁
  refine le_antisymm ?_ ?_
  · rw [spFix_eq_closure_spRadFix hf hnd hF hdim hpF hxpF hpxp, Subgroup.closure_le]
    rintro s (hs | hs)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hs)
    · have h := (map_conj_spRadFix hf hnd hp0 hpF hxS.1 hxS.2 s).mp hs
      have hxG : x ∈ Subgroup.closure (insert x (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      rw [show s = x * (x⁻¹ * s * x) * x⁻¹ by group]
      exact mul_mem (mul_mem hxG (Subgroup.subset_closure (Set.mem_insert_of_mem _ h)))
        (inv_mem hxG)
  · rw [Subgroup.closure_le]
    rintro t (rfl | ht)
    · exact hxS
    · exact spRadFix_le_spFix F p ht

end S2

end CFSG.LargeExtraspecial
