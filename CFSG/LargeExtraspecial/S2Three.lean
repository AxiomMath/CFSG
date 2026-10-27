module

public import CFSG.LargeExtraspecial.S2SpB1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

theorem sp_stab_invariant (hf : f.IsAlt) (hnd : f.Nondegenerate) {a : V} (ha0 : a ≠ 0)
    {S : Submodule (ZMod 2) V}
    (hS : ∀ g ∈ TauCeti.BilinForm.isometryGroup f, g a = a → ∀ x ∈ S, g x ∈ S) :
    S = ⊥ ∨ S = (ZMod 2) ∙ a ∨ S = spPerp f ((ZMod 2) ∙ a) ∨ S = ⊤ := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  have htop : ∀ x : V, x ∈ spPerp f (⊥ : Submodule (ZMod 2) V) := fun x => by
    rw [spPerp_bot]
    exact Submodule.mem_top
  have hmem : ∀ x : V, x ∈ spPerp f ((ZMod 2) ∙ a) ↔ f a x = 0 := fun x => by
    rw [mem_spPerp]
    constructor
    · exact fun h => h a (Submodule.mem_span_singleton_self a)
    · intro h y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, LinearMap.smul_apply, h, smul_zero]
  by_cases h1 : ∃ x ∈ S, f a x = 1
  · obtain ⟨x, hxS, hx⟩ := h1
    right; right; right
    rw [eq_top_iff]
    have hone : ∀ y, f a y = 1 → y ∈ S := by
      intro y hy
      obtain ⟨t, ht, hty⟩ := exists_mem_spRadFix_apply_eq hf (htop a) (htop x) (htop y) hx hy
      rw [← hty]
      exact hS t ht.1.1 ht.1.2.1 x hxS
    intro y _
    rcases zmod2_eq_zero_or_eq_one (f a y) with h0 | h1'
    · have hxy : x + y ∈ S := hone _ (by rw [map_add, hx, h0, add_zero])
      have := S.sub_mem hxy hxS
      rwa [add_sub_cancel_left] at this
    · exact hone y h1'
  push Not at h1
  have hSperp : ∀ x ∈ S, f a x = 0 := fun x hx =>
    (zmod2_eq_zero_or_eq_one _).resolve_right (h1 x hx)
  by_cases h2 : ∃ x ∈ S, x ∉ (ZMod 2) ∙ a
  · obtain ⟨x, hxS, hxa⟩ := h2
    right; right; left
    have hx0 : x ≠ 0 := fun h => hxa (by rw [h]; exact Submodule.zero_mem _)
    have hxne : x ≠ a := fun h => hxa (by rw [h]; exact Submodule.mem_span_singleton_self a)
    have hgood : ∀ y, f a y = 0 → y ∉ (ZMod 2) ∙ a → y ∈ S := by
      intro y hy hya
      have hy0 : y ≠ 0 := fun h => hya (by rw [h]; exact Submodule.zero_mem _)
      have hyne : y ≠ a := fun h => hya (by rw [h]; exact Submodule.mem_span_singleton_self a)
      obtain ⟨g, hg, hga, hgx⟩ := exists_mem_spRadGen_apply_eq_orth hf hnd hF (htop a) (htop x)
        (htop a) (htop y) ha0 hx0 ha0 hy0 (hSperp x hxS) hxne hy hyne
      rw [← hgx]
      exact hS g (spRadGen_le_spFix ⊥ hg).1 hga x hxS
    refine le_antisymm (fun y hy => (hmem y).mpr (hSperp y hy)) fun y hy => ?_
    rw [hmem] at hy
    by_cases hya : y ∈ (ZMod 2) ∙ a
    · rcases mem_span_singleton_iff.mp hya with h0 | h0
      · rw [h0]
        exact S.zero_mem
      · rw [h0] at hy ⊢
        have hax : a + x ∈ S := hgood _ (by rw [map_add, hy, hSperp x hxS, add_zero])
          (fun h => hxa (by
            have := Submodule.sub_mem _ h (Submodule.mem_span_singleton_self a)
            rwa [add_sub_cancel_left] at this))
        have := S.sub_mem hax hxS
        rwa [add_sub_cancel_right] at this
    · exact hgood y hy hya
  · push Not at h2
    by_cases haS : a ∈ S
    · right; left
      exact le_antisymm h2 ((Submodule.span_singleton_le_iff_mem a S).mpr haS)
    · left
      rw [eq_bot_iff]
      intro y hy
      rcases mem_span_singleton_iff.mp (h2 y hy) with h | h
      · exact (Submodule.mem_bot _).mpr h
      · exact absurd (h ▸ hy) haS

theorem sp_finrank_stab_invariant (hf : f.IsAlt) (hnd : f.Nondegenerate) {a : V} (ha0 : a ≠ 0)
    {S : Submodule (ZMod 2) V}
    (hS : ∀ g ∈ TauCeti.BilinForm.isometryGroup f, g a = a → ∀ x ∈ S, g x ∈ S) :
    finrank (ZMod 2) S ≤ 1 ∨ finrank (ZMod 2) V ≤ finrank (ZMod 2) S + 1 := by
  rcases sp_stab_invariant hf hnd ha0 hS with rfl | rfl | rfl | rfl
  · left
    rw [finrank_bot]
    omega
  · left
    rw [finrank_span_singleton ha0]
  · right
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, finrank_span_singleton ha0]
    omega
  · right
    rw [finrank_top]
    omega

theorem sp_even_finrank_spPerp (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    ∀ (n : ℕ) (F : Submodule (ZMod 2) V), F ⊓ spPerp f F = ⊥ →
      finrank (ZMod 2) (spPerp f F) = n → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF hn
  by_cases hne : spPerp f F = ⊥
  · rw [hne, finrank_bot] at hn
    rw [← hn]
    exact even_iff_two_dvd.mpr (dvd_zero 2)
  obtain ⟨p, hpF, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨p₁, hp₁F, hpp₁⟩ := sp_exists_partner hf hnd hF hpF hp0
  have hK := sup_span_pair_inf_spPerp_eq_bot hf hF hpF hp₁F hpp₁
  have hKdim := finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
  have h := ih (n - 2) (by omega) _ hK (by omega)
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by omega⟩

theorem sp_even_finrank (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    Even (finrank (ZMod 2) V) := by
  have := sp_even_finrank_spPerp hf hnd _ ⊥ (bot_inf_eq _) rfl
  rwa [spPerp_bot, finrank_top] at this

section Dim

variable {M W : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable [AddCommGroup W] [Module (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_map_add_finrank_inf_ker (φ : M →ₗ[ZMod 2] W) (D : Submodule (ZMod 2) M) :
    finrank (ZMod 2) (D.map φ) + finrank (ZMod 2) ↥(D ⊓ LinearMap.ker φ) =
      finrank (ZMod 2) D := by
  have h := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict D)
  rw [LinearMap.range_domRestrict] at h
  have hk : (LinearMap.ker (φ.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker φ := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply,
      Submodule.coe_subtype, Submodule.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hv, hv'⟩
      exact ⟨⟨v, hv⟩, hv', rfl⟩
  rw [← hk, Submodule.finrank_map_subtype_eq]
  exact h

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_comap_of_le_range (φ : M →ₗ[ZMod 2] M) {Z : Submodule (ZMod 2) M}
    (hZ : Z ≤ LinearMap.range φ) :
    finrank (ZMod 2) (Z.comap φ) = finrank (ZMod 2) (LinearMap.ker φ) + finrank (ZMod 2) Z := by
  have h := finrank_map_add_finrank_inf_ker φ (Z.comap φ)
  rw [Submodule.map_comap_eq, inf_eq_right.mpr hZ,
    inf_eq_right.mpr (fun v hv => by
      rw [Submodule.mem_comap, LinearMap.mem_ker.mp hv]
      exact Z.zero_mem)] at h
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_le_finrank_add_one {Z : Submodule (ZMod 2) M} (hZ : Z ≠ ⊥) :
    ∃ Y ≤ Z, finrank (ZMod 2) Y + 1 = finrank (ZMod 2) Z := by
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl ((ZMod 2) ∙ z)
  refine ⟨C ⊓ Z, inf_le_right, ?_⟩
  have h1 : (ZMod 2) ∙ z ⊔ C ⊓ Z = Z := by
    rw [← sup_inf_assoc_of_le C ((Submodule.span_singleton_le_iff_mem z Z).mpr hz),
      hC.sup_eq_top, top_inf_eq]
  have h2 : (ZMod 2) ∙ z ⊓ (C ⊓ Z) = ⊥ :=
    eq_bot_iff.mpr (le_trans (inf_le_inf_left _ inf_le_left) hC.inf_eq_bot.le)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq ((ZMod 2) ∙ z) (C ⊓ Z)
  rw [h1, h2, finrank_bot, add_zero, finrank_span_singleton hz0] at h3
  omega

end Dim

section Module

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

@[expose] def IsIndecomposable {G : Type*} [Group G] (ρ : G →* (M ≃ₗ[ZMod 2] M)) : Prop :=
  ∀ A B : Submodule (ZMod 2) M, (∀ g, ∀ v ∈ A, ρ g v ∈ A) → (∀ g, ∀ v ∈ B, ρ g v ∈ B) →
    IsCompl A B → A = ⊥ ∨ B = ⊥

@[expose] noncomputable def spT (hf : f.IsAlt) (a : V) : TauCeti.BilinForm.isometryGroup f :=
  ⟨spTransvection f hf a, spTransvection_mem_isometryGroup hf a⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem spT_apply (hf : f.IsAlt) (a x : V) : (spT hf a : V ≃ₗ[ZMod 2] V) x = x + f x a • a :=
  spTransvection_apply hf a x

omit [FiniteDimensional (ZMod 2) V] in
theorem spT_conj (hf : f.IsAlt) (g : TauCeti.BilinForm.isometryGroup f) (a : V) :
    g * spT hf a * g⁻¹ = spT hf ((g : V ≃ₗ[ZMod 2] V) a) := by
  refine Subtype.ext ?_
  change (g : V ≃ₗ[ZMod 2] V) * spTransvection f hf a * (g : V ≃ₗ[ZMod 2] V)⁻¹ =
    spTransvection f hf ((g : V ≃ₗ[ZMod 2] V) a)
  rw [← spSiegel_zero_one, ← spSiegel_zero_one, spSiegel_conj hf g.2 (map_zero _), map_zero]

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) M] in
theorem rho_spT_sub (hf : f.IsAlt) (g : TauCeti.BilinForm.isometryGroup f) (a : V) (v : M) :
    ρ g (ρ (spT hf a) v - v) =
      ρ (spT hf ((g : V ≃ₗ[ZMod 2] V) a)) (ρ g v) - ρ g v := by
  rw [← spT_conj hf g a, map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply', map_sub]

theorem sp_commSpace_spT_inf_ker (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V) {π : M →ₗ[ZMod 2] V} (hπ : Function.Surjective π)
    (hπρ : ∀ g v, π (ρ g v) = (g : V ≃ₗ[ZMod 2] V) (π v))
    (hker : LinearMap.ker π = fixOf ρ Set.univ) {a : V} (ha0 : a ≠ 0) :
    commSpace (ρ (spT hf a)) ⊓ LinearMap.ker π = ⊥ := by
  set δ : M →ₗ[ZMod 2] M := (ρ (spT hf a) : M →ₗ[ZMod 2] M) - 1 with hδ
  set D := commSpace (ρ (spT hf a)) with hD
  have hDδ : D = LinearMap.range δ := rfl
  have hπδ : ∀ v, π (δ v) = f (π v) a • a := fun v => by
    rw [hδ, LinearMap.sub_apply, map_sub, LinearEquiv.coe_coe, hπρ, spT_apply,
      Module.End.one_apply, add_sub_cancel_left]
  by_contra hne
  obtain ⟨Z, hZle, hZdim⟩ := exists_le_finrank_add_one hne
  have hZker : Z ≤ LinearMap.ker π := hZle.trans inf_le_right
  have hπD : D.map π = (ZMod 2) ∙ a := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      rw [show ((ρ (spT hf a) : M →ₗ[ZMod 2] M) - 1) v = δ v from rfl, hπδ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨x, hx⟩ : ∃ x, f x a ≠ 0 := by
        by_contra! h
        exact ha0 (hnd.2 a h)
      obtain ⟨v, rfl⟩ := hπ x
      refine ⟨δ v, ⟨v, rfl⟩, ?_⟩
      rw [hπδ, zmod2_eq_one_of_ne_zero hx, one_smul]
  have h1 := finrank_map_add_finrank_inf_ker π D
  rw [hπD, finrank_span_singleton ha0] at h1
  have hZD : Z ≤ LinearMap.range δ := hZle.trans inf_le_left
  have h2 := finrank_comap_of_le_range δ hZD
  have h3 := LinearMap.finrank_range_add_finrank_ker δ
  have hkerle : LinearMap.ker π ≤ Z.comap δ := by
    intro v hv
    rw [hker] at hv
    rw [Submodule.mem_comap, hδ, LinearMap.sub_apply, LinearEquiv.coe_coe, hv (spT hf a) trivial,
      Module.End.one_apply, sub_self]
    exact Z.zero_mem
  have h4' := finrank_map_add_finrank_inf_ker π (Z.comap δ)
  rw [inf_eq_right.mpr hkerle] at h4'
  have h5 := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top] at h5
  have hDr : finrank (ZMod 2) D = finrank (ZMod 2) (LinearMap.range δ) := by rw [hDδ]
  have hdimD : finrank (ZMod 2) ((Z.comap δ).map π) + 2 = finrank (ZMod 2) V := by
    omega
  have hinv : ∀ g ∈ TauCeti.BilinForm.isometryGroup f, g a = a →
      ∀ x ∈ (Z.comap δ).map π, g x ∈ (Z.comap δ).map π := by
    rintro g hg hga _ ⟨v, hv, rfl⟩
    set g' : TauCeti.BilinForm.isometryGroup f := ⟨g, hg⟩
    refine ⟨ρ g' v, ?_, hπρ g' v⟩
    change δ (ρ g' v) ∈ Z
    replace hv : δ v ∈ Z := hv
    have e : δ (ρ g' v) = ρ g' (δ v) := by
      have := rho_spT_sub ρ hf g' a v
      rw [show (g' : V ≃ₗ[ZMod 2] V) a = a from hga] at this
      exact this.symm
    rw [e]
    have hfix := hZker hv
    rw [hker] at hfix
    rw [hfix g' trivial]
    exact hv
  rcases sp_finrank_stab_invariant hf hnd ha0 hinv with h | h <;> omega

theorem sp_timmesfeld_2_3_1 (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V) (hind : IsIndecomposable ρ) {π : M →ₗ[ZMod 2] V}
    (hπ : Function.Surjective π) (hπρ : ∀ g v, π (ρ g v) = (g : V ≃ₗ[ZMod 2] V) (π v))
    (hker : LinearMap.ker π = fixOf ρ Set.univ) :
    finrank (ZMod 2) (fixOf ρ Set.univ : Submodule (ZMod 2) M) ≤ 1 := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  have htop : ∀ x : V, x ∈ spPerp f (⊥ : Submodule (ZMod 2) V) := fun x => by
    rw [spPerp_bot]
    exact Submodule.mem_top
  have hfix : ∀ v ∈ LinearMap.ker π, ∀ g, ρ g v = v := fun v hv g => by
    rw [hker] at hv
    exact hv g trivial
  set δ : V → M →ₗ[ZMod 2] M := fun a => (ρ (spT hf a) : M →ₗ[ZMod 2] M) - 1 with hδ
  have hπδ : ∀ a v, π (δ a v) = f (π v) a • a := fun a v => by
    rw [hδ, LinearMap.sub_apply, map_sub, LinearEquiv.coe_coe, hπρ, spT_apply,
      Module.End.one_apply, add_sub_cancel_left]
  have hex : ∀ a : V, a ≠ 0 → ∃ m ∈ LinearMap.range (δ a), π m = a := by
    intro a ha0
    obtain ⟨x, hx⟩ : ∃ x, f x a ≠ 0 := by
      by_contra! h
      exact ha0 (hnd.2 a h)
    obtain ⟨v, rfl⟩ := hπ x
    exact ⟨δ a v, ⟨v, rfl⟩, by rw [hπδ, zmod2_eq_one_of_ne_zero hx, one_smul]⟩
  have huniq : ∀ a : V, a ≠ 0 → ∀ m₁ ∈ LinearMap.range (δ a), ∀ m₂ ∈ LinearMap.range (δ a),
      π m₁ = π m₂ → m₁ = m₂ := by
    intro a ha0 m₁ hm₁ m₂ hm₂ h
    have h0 := sp_commSpace_spT_inf_ker ρ hf hnd h4 hπ hπρ hker ha0
    have : m₁ - m₂ ∈ commSpace (ρ (spT hf a)) ⊓ LinearMap.ker π :=
      ⟨Submodule.sub_mem _ hm₁ hm₂, LinearMap.mem_ker.mpr (by rw [map_sub, h, sub_self])⟩
    rw [h0, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  classical
  let μ : V → M := fun a => if h : a ≠ 0 then Classical.choose (hex a h) else 0
  have hμ : ∀ a, a ≠ 0 → μ a ∈ LinearMap.range (δ a) ∧ π (μ a) = a := fun a ha => by
    simp only [μ, dite_eq_left ha]
    exact Classical.choose_spec (hex a ha)
  have hμ0 : μ 0 = 0 := by simp [μ]
  have hπμ : ∀ a, π (μ a) = a := fun a => by
    by_cases ha : a = 0
    · rw [ha, hμ0, map_zero]
    · exact (hμ a ha).2
  have hμu : ∀ a, a ≠ 0 → ∀ m ∈ LinearMap.range (δ a), π m = a → m = μ a :=
    fun a ha m hm hma => huniq a ha m hm _ (hμ a ha).1 (by rw [hma, (hμ a ha).2])
  have hδmap : ∀ g a v, ρ g (δ a v) = δ ((g : V ≃ₗ[ZMod 2] V) a) (ρ g v) := fun g a v =>
    rho_spT_sub ρ hf g a v
  have hequiv : ∀ g (a : V), ρ g (μ a) = μ ((g : V ≃ₗ[ZMod 2] V) a) := by
    intro g a
    by_cases ha : a = 0
    · rw [ha, hμ0, map_zero, map_zero, hμ0]
    have hga : (g : V ≃ₗ[ZMod 2] V) a ≠ 0 := fun h => ha (g.1.map_eq_zero_iff.mp h)
    obtain ⟨⟨v, hv⟩, -⟩ := hμ a ha
    refine hμu _ hga _ ⟨ρ g v, ?_⟩ (by rw [hπρ, hπμ])
    rw [← hδmap, hv]
  have hadd1 : ∀ a b : V, a ≠ 0 → b ≠ 0 → f a b = 1 → μ (a + b) = μ a + μ b := by
    intro a b ha hb hab
    have h1 : μ (a + b) = ρ (spT hf b) (μ a) := by
      rw [hequiv, spT_apply, hab, one_smul]
    have h2 : δ b (μ a) = μ b :=
      hμu b hb _ ⟨μ a, rfl⟩ (by rw [hπδ, hπμ, hab, one_smul])
    rw [h1, ← h2, hδ]
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    abel
  have hdef : ∀ a b a' b' : V, a ≠ 0 → b ≠ 0 → a' ≠ 0 → b' ≠ 0 → f a b = 0 → b ≠ a →
      f a' b' = 0 → b' ≠ a' → μ (a + b) - μ a - μ b = μ (a' + b') - μ a' - μ b' := by
    intro a b a' b' ha hb ha' hb' hab hne hab' hne'
    obtain ⟨g, hg, hga, hgb⟩ := exists_mem_spRadGen_apply_eq_orth hf hnd hF (htop a) (htop b)
      (htop a') (htop b') ha hb ha' hb' hab hne hab' hne'
    set g' : TauCeti.BilinForm.isometryGroup f := ⟨g, (spRadGen_le_spFix ⊥ hg).1⟩
    have hd : μ (a + b) - μ a - μ b ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, map_sub, hπμ, hπμ, hπμ]
      abel
    rw [← hfix _ hd g', map_sub, map_sub, hequiv, hequiv, hequiv]
    change μ (g (a + b)) - μ (g a) - μ (g b) = _
    rw [map_add, hga, hgb]
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : V, a₀ ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)).mp (by omega)
  obtain ⟨b₀, hb₀perp, hb₀⟩ : ∃ b₀ ∈ spPerp f ((ZMod 2) ∙ a₀), b₀ ∉ (ZMod 2) ∙ a₀ := by
    by_contra! h
    have hle := Submodule.finrank_mono h
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, finrank_span_singleton ha₀] at hle
    omega
  have hab₀ : f a₀ b₀ = 0 := (mem_spPerp.mp hb₀perp) a₀ (Submodule.mem_span_singleton_self a₀)
  have hb₀0 : b₀ ≠ 0 := fun h => hb₀ (by rw [h]; exact Submodule.zero_mem _)
  have hb₀a₀ : b₀ ≠ a₀ := fun h => hb₀ (by rw [h]; exact Submodule.mem_span_singleton_self a₀)
  set d₀ := μ (a₀ + b₀) - μ a₀ - μ b₀ with hd₀
  set W := Submodule.span (ZMod 2) (Set.range μ) with hW
  have hkey : ∀ x y : V, μ x + μ y - μ (x + y) ∈ (ZMod 2) ∙ d₀ := by
    intro x y
    by_cases hx : x = 0
    · rw [hx, hμ0, zero_add, zero_add, sub_self]
      exact Submodule.zero_mem _
    by_cases hy : y = 0
    · rw [hy, hμ0, add_zero, add_zero, sub_self]
      exact Submodule.zero_mem _
    by_cases hxy : y = x
    · rw [hxy, vec_add_self x, hμ0, sub_zero, vec_add_self]
      exact Submodule.zero_mem _
    rcases zmod2_eq_zero_or_eq_one (f x y) with h0 | h1
    · have := hdef x y a₀ b₀ hx hy ha₀ hb₀0 h0 hxy hab₀ hb₀a₀
      have e : μ x + μ y - μ (x + y) = d₀ := by
        rw [hd₀, ← this, vec_sub, vec_sub, vec_sub]
        abel
      rw [e]
      exact Submodule.mem_span_singleton_self d₀
    · rw [hadd1 x y hx hy h1, sub_self]
      exact Submodule.zero_mem _
  have hrep : ∀ w ∈ W, ∃ x : V, w - μ x ∈ (ZMod 2) ∙ d₀ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, rfl⟩ := hw
      exact ⟨a, by rw [sub_self]; exact Submodule.zero_mem _⟩
    | zero => exact ⟨0, by rw [hμ0, sub_self]; exact Submodule.zero_mem _⟩
    | add w₁ w₂ _ _ ih₁ ih₂ =>
      obtain ⟨x₁, h₁⟩ := ih₁
      obtain ⟨x₂, h₂⟩ := ih₂
      refine ⟨x₁ + x₂, ?_⟩
      have e : w₁ + w₂ - μ (x₁ + x₂) =
          (w₁ - μ x₁) + (w₂ - μ x₂) + (μ x₁ + μ x₂ - μ (x₁ + x₂)) := by abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.add_mem _ h₁ h₂) (hkey x₁ x₂)
    | smul c w _ ih =>
      obtain ⟨x, h⟩ := ih
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · exact ⟨0, by rw [zero_smul, hμ0, sub_self]; exact Submodule.zero_mem _⟩
      · exact ⟨x, by rw [one_smul]; exact h⟩
  have hd₀ker : (ZMod 2) ∙ d₀ ≤ LinearMap.ker π := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hd₀, map_sub, map_sub, hπμ,
      hπμ, hπμ]
    abel
  have hWker : W ⊓ LinearMap.ker π ≤ (ZMod 2) ∙ d₀ := by
    rintro w ⟨hw, hwk⟩
    obtain ⟨x, hx⟩ := hrep w hw
    have hx0 : x = 0 := by
      have h1 := hd₀ker hx
      rw [LinearMap.mem_ker, map_sub, LinearMap.mem_ker.mp hwk, hπμ, zero_sub, neg_eq_zero] at h1
      exact h1
    rw [hx0, hμ0, sub_zero] at hx
    exact hx
  have hWsup : W ⊔ LinearMap.ker π = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : μ (π v) ∈ W := Submodule.subset_span ⟨π v, rfl⟩
    have h2 : v - μ (π v) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hπμ, sub_self]
    have := Submodule.add_mem_sup h1 h2
    rwa [add_sub_cancel] at this
  have hWinv : ∀ g, ∀ v ∈ W, ρ g v ∈ W := by
    intro g v hv
    have hle : W ≤ W.comap (ρ g : M →ₗ[ZMod 2] M) := by
      rw [hW, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hequiv]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact hle hv
  obtain ⟨C₁, hC₁⟩ := Submodule.exists_isCompl (W ⊓ LinearMap.ker π)
  set C := C₁ ⊓ LinearMap.ker π with hC
  have hkerdec : W ⊓ LinearMap.ker π ⊔ C = LinearMap.ker π := by
    rw [hC, ← sup_inf_assoc_of_le C₁ inf_le_right, hC₁.sup_eq_top, top_inf_eq]
  have hcompl : IsCompl W C := by
    constructor
    · rw [disjoint_iff, eq_bot_iff, ← hC₁.inf_eq_bot]
      rintro v ⟨hvW, hvC₁, hvk⟩
      exact ⟨⟨hvW, hvk⟩, hvC₁⟩
    · rw [codisjoint_iff, eq_top_iff, ← hWsup]
      refine sup_le le_sup_left ?_
      rw [← hkerdec]
      exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hCinv : ∀ g, ∀ v ∈ C, ρ g v ∈ C := fun g v hv => by
    rw [hfix v hv.2 g]
    exact hv
  rcases hind W C hWinv hCinv hcompl with hW0 | hC0
  · exfalso
    have : μ a₀ ∈ W := Submodule.subset_span ⟨a₀, rfl⟩
    rw [hW0, Submodule.mem_bot] at this
    have h := hπμ a₀
    rw [this, map_zero] at h
    exact ha₀ h.symm
  · rw [hC0, sup_bot_eq] at hkerdec
    rw [← hker, ← hkerdec]
    exact (Submodule.finrank_mono hWker).trans
      (by simpa using finrank_span_le_card ({d₀} : Set M))

omit [FiniteDimensional (ZMod 2) M] in
theorem sp_le_closure_spTransvection (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    TauCeti.BilinForm.isometryGroup f ≤ Subgroup.closure (Set.range (spTransvection f hf)) := by
  set T := Subgroup.closure (Set.range (spTransvection f hf)) with hT
  have hTa : ∀ a, spTransvection f hf a ∈ T := fun a => Subgroup.subset_closure ⟨a, rfl⟩
  have hrad : ∀ p : V, p ≠ 0 → spPointRadical f p ≤ T := by
    intro p hp0 t ht
    obtain ⟨u, hpu, c, rfl⟩ := (mem_spPointRadical_iff hf hnd hp0).mp ht
    have h0 : spSiegel f hf p u 0 ∈ T := by
      have e : spSiegel f hf p u 0 =
          spTransvection f hf p * spTransvection f hf u * spTransvection f hf (p + u) := by
        ext x
        have hup : f u p = 0 := by rw [isAlt_symm hf, hpu]
        rw [spSiegel_apply hf hpu, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          spTransvection_apply, spTransvection_apply, spTransvection_apply]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hf.self_eq_zero, hpu, hup, mul_zero, add_zero, zero_mul]
        refine eq_of_one_smul_eq ?_
        match_scalars <;> ring_nf <;> reduce_mod_char
      rw [e]
      exact mul_mem (mul_mem (hTa p) (hTa u)) (hTa (p + u))
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · exact h0
    · have e : spSiegel f hf p u 1 = spSiegel f hf p u 0 * spTransvection f hf p := by
        rw [← spSiegel_one_mul_zero_one hf hpu, mul_assoc, spSiegel_zero_one,
          ← spSiegel_zero_one, spSiegel_mul_self hf (map_zero _), mul_one]
      rw [e]
      exact mul_mem h0 (hTa p)
  have hgen := spFix_le_spRadGen hf hnd (finrank (ZMod 2) V / 2) ⊥ (bot_inf_eq _) (by
    rw [spPerp_bot, finrank_top]
    obtain ⟨b, hb⟩ := sp_even_finrank hf hnd
    omega)
  rw [spFix_bot] at hgen
  refine hgen.trans ?_
  rw [spRadGen, Subgroup.closure_le]
  rintro t ⟨p, -, hp0, ht⟩
  exact hrad p hp0 (by rw [← spRadFix_bot]; exact ht)

end Module

end S2

end CFSG.LargeExtraspecial
