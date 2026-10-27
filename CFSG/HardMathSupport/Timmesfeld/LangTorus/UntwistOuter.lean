module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE
open scoped commutatorElement

set_option linter.unusedSectionVars false

section UntwistOuter

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem conj_mem_closure_reflections_of_stable {Ψ : Set (Fin τ.rank → ℤ)} (gw : WeylGroup τ)
    (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) (hg : ∀ γ ∈ Ψ, gw⁻¹ • γ ∈ Ψ) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {t : WeylGroup τ | ∃ γ ∈ Ψ, t = rootReflection γ}) :
    gw⁻¹ * w * gw ∈ Subgroup.closure {t : WeylGroup τ | ∃ γ ∈ Ψ, t = rootReflection γ} := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    have h1 := rootReflection_smul_root gw⁻¹ (hΨ γ hγ)
    apply Subgroup.subset_closure
    exact ⟨gw⁻¹ • γ, hg γ hγ, by rw [h1, inv_inv]⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have : gw⁻¹ * (x * y) * gw = (gw⁻¹ * x * gw) * (gw⁻¹ * y * gw) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : gw⁻¹ * x⁻¹ * gw = (gw⁻¹ * x * gw)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem exists_untwist_outer_chi {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ (n : ℕ) {γ : Fin τ.rank → ℤ}, γ ∈ kernelRoots χ →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {s : ℕ} (hs : 0 < s)
    (c₀ : ModGL τ L) (hc₀ : c₀ ∈ monomialSubgroup τ L) (gw : WeylGroup τ)
    (hcg : weylQuotientHom τ L ⟨c₀, hc₀⟩ = gw)
    (hgΨ : ∀ γ ∈ componentRoots χ i,
      gw • γ ∈ componentRoots χ i ∧ gw⁻¹ • γ ∈ componentRoots χ i)
    (hout : ∃ w ∈ Subgroup.closure
        {t : WeylGroup τ | ∃ γ ∈ componentRoots χ i, t = rootReflection γ},
      ∀ γ ∈ componentRoots χ i,
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ = w • (gw • γ)) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      (∀ j : KernelComponent χ, ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots χ j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots χ i),
        iterHom S.D.step s (z * g * z⁻¹) = z * (c₀ * frobGL σ g * c₀⁻¹) * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  set φ : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hφdef
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  obtain ⟨w, hw, hwγ⟩ := hout
  have hc₀inv : c₀⁻¹ ∈ monomialSubgroup τ L := inv_mem hc₀
  have hπinv : weylQuotientHom τ L ⟨c₀⁻¹, hc₀inv⟩ = gw⁻¹ := by
    have : (⟨c₀⁻¹, hc₀inv⟩ : monomialSubgroup τ L) = (⟨c₀, hc₀⟩ : monomialSubgroup τ L)⁻¹ := rfl
    rw [this, map_inv, hcg]
  have hmapsc : MapsRootLines c₀ gw := by
    have := mapsRootLines_weylQuotientHom (τ := τ) (R := L) ⟨c₀, hc₀⟩
    rwa [hcg] at this
  let φ' : ModGL τ L →* ModGL τ L := (MulAut.conj c₀⁻¹).toMonoidHom.comp φ
  have hφ'pin : ∀ γ ∈ componentRoots χ i, ∃ m : L, m ≠ 0 ∧
      ∀ c : L, φ' (pinnedX τ L γ c) = pinnedX τ L ((gw⁻¹ * w * gw) • γ) (m * σ c) := by
    intro γ hγ
    have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s hγr
    obtain ⟨ν, hν⟩ := monomial_conj_pinnedX hc₀inv
      (IsRoot.smul (IsRoot.smul hγr gw) w)
    refine ⟨(ν : L) * μ, mul_ne_zero ν.ne_zero hμ0, fun c => ?_⟩
    show c₀⁻¹ * φ (pinnedX τ L γ c) * c₀⁻¹⁻¹ = _
    rw [hφdef, iterHom_eq_iterate, hμ, hwγ γ hγ, hσc, hν, hπinv]
    simp only [mul_smul, mul_assoc]
  have hw' := conj_mem_closure_reflections_of_stable gw
    (fun γ hγ => isRoot_of_mem_componentRoots hγ) (fun γ hγ => (hgΨ γ hγ).2) hw
  obtain ⟨y', hy', hpin'⟩ := exists_pin i σ φ' hw' hφ'pin
  set y₁ : ModGL τ L := c₀ * y' * c₀⁻¹ with hy₁def
  have hy₁ : y₁ ∈ torusGroup τ L ⊔ rootSpan τ L (componentRoots χ i) := by
    have hmapZ : (torusGroup τ L ⊔ rootSpan τ L (componentRoots χ i)).map
        (MulAut.conj c₀).toMonoidHom ≤
        torusGroup τ L ⊔ rootSpan τ L (componentRoots χ i) := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1
          (mem_normalizer_torusGroup_of_mem_monomialSubgroup hc₀) t).1 ht
      · rintro _ ⟨r, hr, rfl⟩
        have hr' := conj_mem_rootSpan_of_mapsRootLines hc₀ hmapsc
          (S := componentRoots χ i)
          (fun α hα => isRoot_of_mem_componentRoots hα) hr
        exact rootSpan_mono (by
          rintro _ ⟨α, hα, rfl⟩
          exact (hgΨ α hα).1) hr'
    exact hmapZ ⟨y', hy', rfl⟩
  have hpin : ∀ g ∈ rootSpan τ L (componentRoots χ i),
      y₁ * φ g * y₁⁻¹ = c₀ * frobGL σ g * c₀⁻¹ := by
    intro g hg
    have h := hpin' g hg
    change y' * (c₀⁻¹ * φ g * c₀⁻¹⁻¹) * y'⁻¹ = _ at h
    rw [inv_inv] at h
    calc y₁ * φ g * y₁⁻¹ = c₀ * (y' * (c₀⁻¹ * φ g * c₀) * y'⁻¹) * c₀⁻¹ := by
          rw [hy₁def]; group
      _ = c₀ * frobGL σ g * c₀⁻¹ := by rw [h]
  obtain ⟨z, hzZ, hφz⟩ := exists_lang_torus_sup_kernelRoots S hs (fun γ hγ => hker s hγ)
    ((sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hy₁)
  replace hφz : φ z = z * y₁ := hφz
  refine ⟨σ, z, hσc, mem_componentRootSpan_iff_conj_of_mem hzZ, fun g hg => ?_⟩
  · rw [map_mul, map_mul, map_inv, hφz]
    have := hpin g hg
    calc z * y₁ * φ g * (z * y₁)⁻¹ = z * (y₁ * φ g * y₁⁻¹) * z⁻¹ := by group
      _ = z * (c₀ * frobGL σ g * c₀⁻¹) * z⁻¹ := by rw [this]

theorem exists_untwist_outer_T {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hs : 0 < s)
    (c₀ : ModGL τ L) (hc₀ : c₀ ∈ monomialSubgroup τ L) (gw : WeylGroup τ)
    (hcg : weylQuotientHom τ L ⟨c₀, hc₀⟩ = gw)
    (hgΨ : ∀ γ ∈ componentRoots (rootCharHom a) i,
      gw • γ ∈ componentRoots (rootCharHom a) i ∧ gw⁻¹ • γ ∈ componentRoots (rootCharHom a) i)
    (hout : ∃ w ∈ Subgroup.closure
        {t : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i, t = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i,
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ = w • (gw • γ)) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        iterHom S.D.step s (z * g * z⁻¹) = z * (c₀ * frobGL σ g * c₀⁻¹) * z⁻¹ :=
  exists_untwist_outer_chi S (fun n _ hγ => outer_iterate_mem_kernelRoots S hT n hγ) i hs c₀ hc₀ gw hcg
    hgΨ hout

end UntwistOuter

end CFSG.HardMathSupport.Timmesfeld.LangTorus
