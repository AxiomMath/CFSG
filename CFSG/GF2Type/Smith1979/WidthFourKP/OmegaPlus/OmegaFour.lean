module

public import CFSG.LargeExtraspecial.S10Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial

theorem gm_pow_three_of_pow_nine : ∀ δ : S10.Gm, δ ^ 9 = 1 → δ ^ 3 = 1 := by
  decide +kernel

theorem gm_card_pow_three : (Finset.univ.filter fun δ : S10.Gm => δ ^ 3 = 1).card = 9 := by
  decide +kernel

theorem gm_eq_one_of_commute : ∀ γ : S10.Gm, γ ^ 2 = 1 →
    (∀ δ : S10.Gm, δ ^ 3 = 1 → γ * δ = δ * γ) → γ = 1 := by
  decide +kernel

theorem gm_eq_one_of_commute_card_nine {P : Subgroup S10.Gm} (hP : Nat.card P = 9)
    {γ : S10.Gm} (hγ2 : γ ^ 2 = 1) (hγP : ∀ x ∈ P, γ * x = x * γ) : γ = 1 := by
  classical
  have hcube : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => by
    apply gm_pow_three_of_pow_nine
    have h := pow_card_eq_one (G := P) (x := ⟨x, hx⟩)
    rw [← Nat.card_eq_fintype_card, hP] at h
    exact congrArg Subtype.val h
  have hsub : (P : Set S10.Gm).toFinset ⊆ Finset.univ.filter fun δ : S10.Gm => δ ^ 3 = 1 := by
    intro x hx
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcube x hx
  have hcardP : (P : Set S10.Gm).toFinset.card = 9 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hP
  have heq : (P : Set S10.Gm).toFinset = Finset.univ.filter fun δ : S10.Gm => δ ^ 3 = 1 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [gm_card_pow_three, hcardP])
  refine gm_eq_one_of_commute γ hγ2 fun δ hδ => hγP δ ?_
  have hmem : δ ∈ (P : Set S10.Gm).toFinset := by
    rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hδ
  simpa using hmem

section Transport

variable {W W' : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup W']
  [Module (ZMod 2) W']

@[expose] def conjEquiv (e : W ≃ₗ[ZMod 2] W') : (W ≃ₗ[ZMod 2] W) ≃* (W' ≃ₗ[ZMod 2] W') where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := by ext w; simp
  right_inv f := by ext w; simp
  map_mul' f g := by ext w; simp

theorem conjEquiv_apply (e : W ≃ₗ[ZMod 2] W') (f : W ≃ₗ[ZMod 2] W) (w : W') :
    conjEquiv e f w = e (f (e.symm w)) := rfl

theorem commSpace_conjEquiv (e : W ≃ₗ[ZMod 2] W') (f : W ≃ₗ[ZMod 2] W) :
    commSpace (conjEquiv e f) = (commSpace f).map (e : W →ₗ[ZMod 2] W') := by
  ext w
  simp only [commSpace, LinearMap.mem_range, Submodule.mem_map, LinearMap.sub_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, Module.End.one_apply]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨f (e.symm y) - e.symm y, ⟨e.symm y, rfl⟩, ?_⟩
    rw [map_sub, LinearEquiv.apply_symm_apply, conjEquiv_apply]
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨e y, ?_⟩
    rw [conjEquiv_apply, LinearEquiv.symm_apply_apply, map_sub]

variable [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) W']

theorem conjEquiv_mem_omegaGroup {Q : QuadraticForm (ZMod 2) W}
    {Q' : QuadraticForm (ZMod 2) W'} (hQ : Q.polarBilin.Nondegenerate)
    (hQ' : Q'.polarBilin.Nondegenerate) (e : W ≃ₗ[ZMod 2] W') (he : ∀ w, Q' (e w) = Q w)
    {f : W ≃ₗ[ZMod 2] W} (hf : f ∈ omegaGroup Q hQ) : conjEquiv e f ∈ omegaGroup Q' hQ' := by
  rw [mem_omegaGroup] at hf ⊢
  obtain ⟨hO, hE⟩ := hf
  refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => ?_, ?_⟩
  · rw [conjEquiv_apply, he, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO, ← he,
      LinearEquiv.apply_symm_apply]
  · rw [commSpace_conjEquiv, LinearEquiv.finrank_map_eq]
    exact hE

end Transport

theorem eq_one_of_commute_card_nine_omega {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {Q : QuadraticForm (ZMod 2) W}
    (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) W = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {P : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hP : P ≤ omegaGroup Q hQ) (hP9 : Nat.card P = 9) {σ : W ≃ₗ[ZMod 2] W}
    (hσ : σ ∈ omegaGroup Q hQ) (hσ2 : σ ^ 2 = 1) (hσP : ∀ x ∈ P, σ * x = x * σ) : σ = 1 := by
  obtain ⟨e₁⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ (n := 2)
    (by rw [h4]) hplus
  let e : W ≃ₗ[ZMod 2] S10.M2 := e₁.toLinearEquiv.trans S10.plusEquiv
  have he : ∀ w, S10.q₀ (e w) = Q w := fun w => by
    change S10.q₀ (S10.plusEquiv (e₁ w)) = Q w
    rw [S10.q₀_plusEquiv, e₁.map_app]
  have hmem : ∀ f ∈ omegaGroup Q hQ, conjEquiv e f ∈ S10.ρ₀.range := fun f hf => by
    rw [S10.range_ρ₀]
    exact conjEquiv_mem_omegaGroup hQ S10.q₀_nondegenerate e he hf
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp (hmem σ hσ)
  let P' : Subgroup S10.Gm := (P.map (conjEquiv e).toMonoidHom).comap S10.ρ₀
  have hP'card : Nat.card P' = 9 := by
    have hle : P.map (conjEquiv e).toMonoidHom ≤ S10.ρ₀.range := by
      rintro _ ⟨f, hf, rfl⟩
      exact hmem f (hP hf)
    have h1 : Nat.card (P.map (conjEquiv e).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (conjEquiv e).injective, hP9]
    have h2 := Subgroup.map_comap_eq_self hle
    rw [← h1, ← h2, Subgroup.card_map_of_injective S10.ρ₀_injective]
  have hγ1 : γ = 1 := by
    refine gm_eq_one_of_commute_card_nine hP'card ?_ fun x hx => ?_
    · apply S10.ρ₀_injective
      rw [map_pow, hγ, map_one, ← map_pow, hσ2, map_one]
    · obtain ⟨f, hf, hfx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
      apply S10.ρ₀_injective
      rw [map_mul, map_mul, hγ, ← hfx]
      change conjEquiv e σ * conjEquiv e f = conjEquiv e f * conjEquiv e σ
      rw [← map_mul, ← map_mul, hσP f hf]
  rw [hγ1, map_one] at hγ
  exact (conjEquiv e).injective (by rw [← hγ, map_one])

end CFSG.GF2Type.Smith1979.OmegaPlus
