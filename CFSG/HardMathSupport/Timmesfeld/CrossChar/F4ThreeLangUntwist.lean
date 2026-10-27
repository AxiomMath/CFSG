module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem f4Three_exists_conj_pinnedX_neg {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    ∃ ε : L, ε * ε = 1 ∧ ∀ t : L,
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ * pinnedX τ L (-δ) t *
          canonicalRep (coxeterSystem τ) L w₀ = pinnedX τ L δ (ε * t) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w₀ hδ
  refine ⟨ε, hε, fun t => ?_⟩
  have h1 := h (ε * t)
  rw [hw₀, ← mul_assoc, hε, one_mul] at h1
  rw [← h1]
  group

theorem f4Three_exists_untwist_neg {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    {a : Fin τ.rank → Lˣ} (hE : rootDiagUnit τ a ∈ S.E) (i : KernelComponent (rootCharHom a))
    {u : WeylGroup τ}
    (hu : u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
      s = rootReflection γ})
    (hρu : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ)) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ S.D.q) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        S.D.step (z * g * z⁻¹) = z * (canonicalRep (coxeterSystem τ) L w₀ * frobGL σ g *
          (canonicalRep (coxeterSystem τ) L w₀)⁻¹) * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r e
  have hσc : ∀ c, σ c = c ^ S.D.q := by
    intro c
    have h1 : σ c = iterateFrobenius L r e c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq]
  set n₀ := canonicalRep (coxeterSystem τ) L w₀ with hn₀
  set φ : ModGL τ L →* ModGL τ L := (MulAut.conj n₀⁻¹).toMonoidHom.comp S.D.step with hφdef
  have hφapp : ∀ g, φ g = n₀⁻¹ * S.D.step g * n₀⁻¹⁻¹ := fun g => rfl
  have hφpin : ∀ γ ∈ componentRoots (rootCharHom a) i, ∃ m : L, m ≠ 0 ∧
      ∀ c : L, φ (pinnedX τ L γ c) = pinnedX τ L (u • γ) (m * σ c) := by
    intro γ hγ
    have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
    obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S hγr
    obtain ⟨ε, hε, hconj⟩ := f4Three_exists_conj_pinnedX_neg (L := L) hw₀ (IsRoot.smul hγr u)
    have hε0 : ε ≠ 0 := fun h0 => by simp [h0] at hε
    refine ⟨ε * μ, mul_ne_zero hε0 hμ0, fun c => ?_⟩
    rw [hφapp, hμ c, hρu γ hγ, inv_inv, hconj, hσc, mul_assoc]
  obtain ⟨y₁, hy₁, hpin⟩ := exists_pin i σ φ hu hφpin
  set χ := rootCharHom a with hχ
  set Z : Subgroup (ModGL τ L) := torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) with hZ
  have hy₁Z : y₁ ∈ Z := (sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hy₁
  have hn₀T : ∀ t ∈ torusGroup τ L, n₀ * t * n₀⁻¹ ∈ torusGroup τ L := fun t ht =>
    (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w₀) t).1 ht
  have hn₀R : ∀ g ∈ rootSpan τ L (kernelRoots χ),
      n₀ * g * n₀⁻¹ ∈ rootSpan τ L (kernelRoots χ) := by
    have hmap : (rootSpan τ L (kernelRoots χ)).map (MulAut.conj n₀).toMonoidHom ≤
        rootSpan τ L (kernelRoots χ) := by
      refine map_rootSpan_le_of_forall fun γ hγ c => ?_
      obtain ⟨ε, -, hε⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w₀ hγ.1
      change n₀ * pinnedX τ L γ c * n₀⁻¹ ∈ _
      rw [hε, hw₀]
      have hneg : -γ ∈ kernelRoots χ := by
        rw [kernelRoots_rootCharHom] at hγ ⊢
        refine ⟨IsRoot.neg hγ.1, ?_⟩
        rw [show -γ = (-1 : ℤ) • γ by rw [neg_one_smul], rootChar_zsmul, hγ.2, one_zpow]
      exact pinnedX_mem_rootSpan hneg _
    exact fun g hg => hmap ⟨g, hg, rfl⟩
  have hn₀Z : n₀ * y₁ * n₀⁻¹ ∈ Z := by
    have hmap : Z.map (MulAut.conj n₀).toMonoidHom ≤ Z := by
      rw [hZ, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        exact hn₀T t ht
      · rintro _ ⟨t, ht, rfl⟩
        exact hn₀R t ht
    exact hmap ⟨y₁, hy₁Z, rfl⟩
  obtain ⟨z, hzZ, hz1⟩ := exists_lang_torus_sup_kernelRoots S one_pos
    (fun γ hγ => by rw [Function.iterate_one]; exact S.rho_mem_kernelRoots hE hγ) hn₀Z
  have hstepz : S.D.step z = z * (n₀ * y₁ * n₀⁻¹) := by
    rw [← hz1, iterHom_eq_iterate, Function.iterate_one]
  refine ⟨σ, z, hσc, mem_componentRootSpan_iff_conj_of_mem hzZ, fun g hg => ?_⟩
  · have hφg : S.D.step g = n₀ * φ g * n₀⁻¹ := by
      rw [hφapp]
      group
    rw [map_mul, map_mul, map_inv, hstepz, hφg]
    have := hpin g hg
    calc z * (n₀ * y₁ * n₀⁻¹) * (n₀ * φ g * n₀⁻¹) * (z * (n₀ * y₁ * n₀⁻¹))⁻¹ =
        z * (n₀ * (y₁ * φ g * y₁⁻¹) * n₀⁻¹) * z⁻¹ := by group
      _ = z * (n₀ * frobGL σ g * n₀⁻¹) * z⁻¹ := by rw [this]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
