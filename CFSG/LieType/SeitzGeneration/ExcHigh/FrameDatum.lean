module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open

@[expose] def FrameDatumIn (G : Type*) [Group G] (p o : ℕ) : Prop :=
  ∃ V₁ V₂ X₁ X₂ : Subgroup G,
    IsElemAbelian p V₁ ∧ IsElemAbelian p V₂ ∧ Nat.card V₁ = p ^ 2 ∧ Nat.card V₂ = p ^ 2 ∧
    Disjoint V₁ V₂ ∧ (∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) ∧
    V₁ ≤ X₁ ∧ V₂ ≤ X₂ ∧
    (∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) ∧
    (∀ g ∈ X₁, ∀ b ∈ V₂, g * b = b * g) ∧ (∀ g ∈ X₂, ∀ b ∈ V₁, g * b = b * g) ∧
    X₁ ≤ Subgroup.closure {g | g ∈ X₁ ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g} ∧
    X₂ ≤ Subgroup.closure {g | g ∈ X₂ ∧ ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g} ∧
    Nat.card X₁ ≤ o ∧ Nat.card X₂ ≤ o ∧
    (∀ H : Subgroup G, X₁ ⊔ X₂ ≤ H →
      ¬ H ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) → H = ⊤) ∧
    (∀ H : Subgroup G, H ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) →
      Group.IsSolvable ↥(H ⊓ (X₁ ⊔ X₂)) → Group.IsSolvable ↥H)

theorem isElemAbelian_image {A B : Type*} [Group A] [Group B] {p : ℕ} (σ : A →* B)
    {V : Subgroup A} (hV : IsElemAbelian p V) : IsElemAbelian p (V.map σ) := by
  haveI := hV.1
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  rw [← map_pow, hV.2 x hx, map_one]

theorem isSolvable_image_of_injective {A B : Type*} [Group A] [Group B] (σ : A →* B)
    (hσ : Function.Injective σ) (K : Subgroup A) [Group.IsSolvable ↥K] :
    Group.IsSolvable ↥(K.map σ) :=
  Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective K σ hσ).toMonoidHom)
    (Subgroup.equivMapOfInjective K σ hσ).surjective

theorem isSolvable_of_image_injective {A B : Type*} [Group A] [Group B] (σ : A →* B)
    (hσ : Function.Injective σ) (K : Subgroup A) (hK : Group.IsSolvable ↥(K.map σ)) :
    Group.IsSolvable ↥K := by
  haveI := hK
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.equivMapOfInjective K σ hσ).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective K σ hσ).symm.surjective

theorem FrameDatumIn.of_bijective {G H : Type*} [Group G] [Group H] (σ : H →* G)
    (hσ : Function.Bijective σ) {p o : ℕ} (h : FrameDatumIn H p o) : FrameDatumIn G p o := by
  obtain ⟨V₁, V₂, X₁, X₂, hV₁, hV₂, hc₁, hc₂, hdisj, hVc, hVX₁, hVX₂, hXc, hX₁V₂, hX₂V₁,
    hcl₁, hcl₂, ho₁, ho₂, hclose, hsolv⟩ := h
  have hinj : Function.Injective σ := hσ.1
  have hsurj : Function.Surjective σ := hσ.2
  have hN : (X₁ ⊔ X₂).map σ = X₁.map σ ⊔ X₂.map σ := Subgroup.map_sup X₁ X₂ σ
  have hcl : ∀ V X : Subgroup H,
      X ≤ Subgroup.closure {g | g ∈ X ∧ ∃ x ∈ V, x ≠ 1 ∧ g * x = x * g} →
      X.map σ ≤
        Subgroup.closure {g : G | g ∈ X.map σ ∧ ∃ x ∈ V.map σ, x ≠ 1 ∧ g * x = x * g} := by
    intro V X hX
    refine (Subgroup.map_mono (f := σ) hX).trans ?_
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨k, ⟨hkX, x, hxV, hx1, hkx⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem σ hkX, σ x, Subgroup.mem_map_of_mem σ hxV,
      fun h1 => hx1 (hinj (h1.trans (map_one σ).symm)), ?_⟩
    rw [← map_mul, ← map_mul, hkx]
  refine ⟨V₁.map σ, V₂.map σ, X₁.map σ, X₂.map σ, isElemAbelian_image σ hV₁,
    isElemAbelian_image σ hV₂, ?_, ?_, Subgroup.disjoint_map hinj hdisj, ?_,
    Subgroup.map_mono hVX₁, Subgroup.map_mono hVX₂, ?_, ?_, ?_, hcl V₁ X₁ hcl₁,
    hcl V₂ X₂ hcl₂, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hc₁]
  · rw [Subgroup.card_map_of_injective hinj, hc₂]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hVc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hXc a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hX₁V₂ a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hX₂V₁ a ha b hb]
  · rw [Subgroup.card_map_of_injective hinj]
    exact ho₁
  · rw [Subgroup.card_map_of_injective hinj]
    exact ho₂
  ·
    intro H' hH' hnot
    rw [← hN] at hH' hnot
    have hK : (H'.comap σ).map σ = H' := Subgroup.map_comap_eq_self_of_surjective hsurj H'
    have hXK : X₁ ⊔ X₂ ≤ H'.comap σ := Subgroup.map_le_iff_le_comap.1 hH'
    have hKn : ¬ H'.comap σ ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup H) : Set H) := by
      intro hle
      apply hnot
      calc H' = (H'.comap σ).map σ := hK.symm
        _ ≤ (Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup H) : Set H)).map σ :=
            Subgroup.map_mono hle
        _ = Subgroup.normalizer (((X₁ ⊔ X₂).map σ : Subgroup G) : Set G) :=
            Subgroup.map_normalizer_eq_of_bijective _ hσ
    calc H' = (H'.comap σ).map σ := hK.symm
      _ = ⊤ := by rw [hclose (H'.comap σ) hXK hKn, Subgroup.map_top_of_surjective σ hsurj]
  ·
    intro H' hH' hsolvH'
    have hK : (H'.comap σ).map σ = H' := Subgroup.map_comap_eq_self_of_surjective hsurj H'
    have hKn : H'.comap σ ≤ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup H) : Set H) := by
      refine (Subgroup.map_le_map_iff_of_injective hinj).1 ?_
      rw [hK, Subgroup.map_normalizer_eq_of_bijective _ hσ, hN]
      exact hH'
    have hmap : (H'.comap σ ⊓ (X₁ ⊔ X₂)).map σ = H' ⊓ (X₁.map σ ⊔ X₂.map σ) := by
      rw [Subgroup.map_inf _ _ σ hinj, hK, hN]
    have hKsolv : Group.IsSolvable ↥(H'.comap σ ⊓ (X₁ ⊔ X₂)) :=
      isSolvable_of_image_injective σ hinj _ (by rw [hmap]; exact hsolvH')
    have hKs : Group.IsSolvable ↥(H'.comap σ) := hsolv (H'.comap σ) hKn hKsolv
    haveI := hKs
    have hfin := isSolvable_image_of_injective σ hinj (H'.comap σ)
    rwa [hK] at hfin

theorem FrameDatumIn.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {p o : ℕ}
    (h : FrameDatumIn H p o) : FrameDatumIn G p o :=
  FrameDatumIn.of_bijective e.symm.toMonoidHom e.symm.bijective h

theorem closure_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (V : Subgroup G)
    (h : Subgroup.closure {k : H | ∃ x ∈ V.map e.toMonoidHom, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    Subgroup.closure {g : G | ∃ x ∈ V, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  have himg : e.symm.toMonoidHom ''
      {k : H | ∃ x ∈ V.map e.toMonoidHom, x ≠ 1 ∧ k * x = x * k} =
      {g : G | ∃ x ∈ V, x ≠ 1 ∧ g * x = x * g} := by
    ext g
    constructor
    · rintro ⟨k, ⟨x', hx', hx'1, hkx⟩, rfl⟩
      obtain ⟨x, hxV, rfl⟩ := Subgroup.mem_map.1 hx'
      refine ⟨x, hxV, fun hx => hx'1 (by rw [hx, map_one]), ?_⟩
      show e.symm k * x = x * e.symm k
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hkx
    · rintro ⟨x, hxV, hx1, hgx⟩
      refine ⟨e g, ⟨e x, Subgroup.mem_map.2 ⟨x, hxV, rfl⟩,
        fun h1 => hx1 (e.injective (h1.trans (map_one e).symm)), ?_⟩, e.symm_apply_apply g⟩
      rw [← map_mul, ← map_mul, hgx]
  rw [← himg, ← MonoidHom.map_closure, h,
    Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]

end CFSG.LieType.SeitzGeneration.ExcHigh
