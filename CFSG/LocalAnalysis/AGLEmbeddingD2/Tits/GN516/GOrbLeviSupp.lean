module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

private theorem weylAction_simple_sign {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) {J : Set I} {m : I} (hm : m ∈ J)
    (hJ : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → A j k = 0) {j : I} (hj : j ∈ J) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple j) (Pi.single m 1) =
        Pi.single m 1 ∨
      weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple j) (Pi.single m 1) =
        -Pi.single m 1 := by
  rcases eq_or_ne j m with hjm | hjm
  · rw [hjm]
    exact Or.inr (weylAction_simple_single hA m)
  · left
    rw [weylAction_simple hA j, reflection_apply_coroot, coroot_single, hJ j hj m hm hjm,
      zero_smul, sub_zero]

private theorem weylAction_mul_sign {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) {m : I} {a b : (coxeterMatrix hA).Group}
    (ha : weylAction hA a (Pi.single m 1) = Pi.single m 1 ∨
      weylAction hA a (Pi.single m 1) = -Pi.single m 1)
    (hb : weylAction hA b (Pi.single m 1) = Pi.single m 1 ∨
      weylAction hA b (Pi.single m 1) = -Pi.single m 1) :
    weylAction hA (a * b) (Pi.single m 1) = Pi.single m 1 ∨
      weylAction hA (a * b) (Pi.single m 1) = -Pi.single m 1 := by
  rw [weylAction_mul_apply]
  rcases hb with hb | hb
  · rw [hb]
    exact ha
  · rw [hb, map_neg]
    rcases ha with ha | ha
    · rw [ha]
      exact Or.inr rfl
    · rw [ha, neg_neg]
      exact Or.inl rfl

private theorem weylAction_parabolic_sign {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) {J : Set I} {m : I} (hm : m ∈ J)
    (hJ : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → A j k = 0) (u : (coxeterMatrix hA).Group)
    (hu : u ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic J) :
    weylAction hA u (Pi.single m 1) = Pi.single m 1 ∨
      weylAction hA u (Pi.single m 1) = -Pi.single m 1 := by
  obtain ⟨ω, hωJ, rfl⟩ :=
    (coxeterMatrix hA).toCoxeterSystem.exists_wordProd_eq_of_mem_parabolic hu
  clear hu
  induction ω with
  | nil =>
    left
    rw [CoxeterSystem.wordProd_nil, map_one, Module.End.one_apply]
  | cons a ω ih =>
    rw [CoxeterSystem.wordProd_cons]
    exact weylAction_mul_sign hA (weylAction_simple_sign hA hm hJ (hωJ a (by simp)))
      (ih fun i hi => hωJ i (by simp [hi]))

private theorem weylAction_single_eq_of_support {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) {J : Set I}
    (hJ : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → A j k = 0) (w : (coxeterMatrix hA).Group) (i : I)
    (hsupp : ∀ k ∉ J, weylAction hA w (Pi.single i 1) k = 0) :
    ∃ j ∈ J, weylAction hA w (Pi.single i 1) = Pi.single j 1 ∨
      weylAction hA w (Pi.single i 1) = -Pi.single j 1 := by
  obtain ⟨z, hz, m, hm, hzm⟩ := exists_parabolic_of_support hA J w i hsupp
  refine ⟨m, hm, ?_⟩
  have hv : weylAction hA w (Pi.single i 1) = weylAction hA z⁻¹ (Pi.single m 1) := by
    rw [← hzm, weylAction_inv_apply_apply]
  rw [hv]
  exact weylAction_parabolic_sign hA hm hJ z⁻¹ (inv_mem hz)

theorem eq_of_support_of_independent {J : Set (Fin D.rank)}
    (hJ : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → D.cartan j k = 0) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hsupp : ∀ k ∉ J, γ k = 0) :
    ∃ j ∈ J, γ = Pi.single j 1 ∨ γ = -Pi.single j 1 ∨ γ = 2 • Pi.single j 1 ∨
      γ = -(2 • Pi.single j 1) := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, -, rfl⟩
  · obtain ⟨j, hj, h | h⟩ := weylAction_single_eq_of_support D.isFiniteType hJ w i hsupp
    · exact ⟨j, hj, Or.inl h⟩
    · exact ⟨j, hj, Or.inr (Or.inl h)⟩
  ·
    have hsupp' : ∀ k ∉ J, weylAction D.isFiniteType w (Pi.single i 1) k = 0 := by
      intro k hk
      have h := hsupp k hk
      simp only [Pi.smul_apply, nsmul_eq_mul] at h
      omega
    obtain ⟨j, hj, h | h⟩ := weylAction_single_eq_of_support D.isFiniteType hJ w i hsupp'
    · exact ⟨j, hj, Or.inr (Or.inr (Or.inl (by rw [h])))⟩
    · exact ⟨j, hj, Or.inr (Or.inr (Or.inr (by rw [h, smul_neg])))⟩

end CFSG.AGLEmbeddingD2.Tits.GN516.Levi
