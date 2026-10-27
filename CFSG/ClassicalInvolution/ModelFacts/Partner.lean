module

public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

section Abstract

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

@[expose] def IsPartner (γ δ : I → ℤ) : Prop :=
  2 * form hA (toRat γ) (toRat δ) = -lenSq hA δ

variable {hA}

theorem IsPartner.symm {γ δ : I → ℤ} (h : IsPartner hA γ δ) (hl : lenSq hA γ = lenSq hA δ) :
    IsPartner hA δ γ := by
  rw [IsPartner, form_comm hA, hl]
  exact h

theorem IsPartner.map_weylAction {γ δ : I → ℤ} (h : IsPartner hA γ δ)
    (w : (coxeterMatrix hA).Group) :
    IsPartner hA (weylAction hA w γ) (weylAction hA w δ) := by
  rw [IsPartner, form_weylAction, lenSq_weylAction]
  exact h

variable (hA)

theorem exists_partner_of_exists (hirr : IsIrreducible A) {D : Set I}
    (hD : ∀ i ∈ D, ∀ j, symmetrizer hA j < 4 * symmetrizer hA i)
    (h₀ : ∃ γ₀ δ₀ : I → ℤ, IsLongest hA D γ₀ ∧ IsLongest hA D δ₀ ∧ IsPartner hA γ₀ δ₀) :
    ∀ γ, IsLongest hA D γ → ∃ δ, IsLongest hA D δ ∧ IsPartner hA γ δ := by
  obtain ⟨γ₀, δ₀, hγ₀, hδ₀, hp⟩ := h₀
  intro γ hγ
  obtain ⟨w, hw⟩ := exists_weylAction_eq_of_isLongest hA hirr hD hγ₀ hγ
  refine ⟨weylAction hA w δ₀, hδ₀.map_weylAction w, ?_⟩
  rw [← hw]
  exact hp.map_weylAction w

theorem form_single_single_apply (i j : I) :
    form hA (toRat (Pi.single i 1)) (toRat (Pi.single j 1)) = symmetrizer hA i * A i j := by
  rw [toRat_single, toRat_single, form_single_left]
  simp [Pi.single_apply]

theorem isPartner_single_single {i j : I} (hij : A i j = -1) (hji : A j i = -1) :
    IsPartner hA (Pi.single i 1) (Pi.single j 1) := by
  have h := symmetrizer_mul_apply hA i j
  rw [hij, hji] at h
  rw [IsPartner, form_single_single_apply, lenSq_single, hij]
  push_cast at h ⊢
  linarith

theorem isPartner_single_reflection {i j : I} (h : A i j * A j i = 3) :
    IsPartner hA (Pi.single i 1)
      (weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple j) (Pi.single i 1)) := by
  have hr : weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple j) (Pi.single i 1) =
      Pi.single i 1 - A j i • (Pi.single j 1 : I → ℤ) := by
    rw [weylAction_simple, reflection_apply_coroot, coroot_single]
  have h' : ((A i j : ℚ) * A j i) = 3 := by exact_mod_cast h
  have h2 : (A i i : ℚ) = 2 := by exact_mod_cast hA.apply_self i
  rw [IsPartner, lenSq_weylAction, hr]
  simp only [map_sub, map_zsmul, form_single_single_apply, lenSq_single]
  rw [zsmul_eq_mul]
  linear_combination (-2 * symmetrizer hA i) * h' + (2 * symmetrizer hA i) * h2

end Abstract

section Group

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_forall_longest_partner
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {γ₀ δ₀ : Fin D.rank → ℤ} (hγ₀ : IsLongestRoot D γ₀) (hδ₀ : IsLongestRoot D δ₀)
    (hp : IsPartner D.isFiniteType γ₀ δ₀) (P : Subgroup K → Subgroup K → Prop)
    (hP : ∀ (g : K) (U V : Subgroup K), P U V →
      P (U.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom))
    (h₀ : P (D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀)) (D.rootGroup δ₀ ⊔ D.rootGroup (-δ₀)))
    {γ : Fin D.rank → ℤ} (hγ : IsLongestRoot D γ) :
    ∃ δ : Fin D.rank → ℤ, IsLongestRoot D δ ∧ IsPartner D.isFiniteType γ δ ∧
      P (D.rootGroup γ ⊔ D.rootGroup (-γ)) (D.rootGroup δ ⊔ D.rootGroup (-δ)) := by
  obtain ⟨w, hw⟩ := exists_weylAction_eq_of_isLongest D.isFiniteType hirr hD hγ₀ hγ
  obtain ⟨g, hg⟩ := exists_map_conj_rankOne hct w
  refine ⟨weylAction D.isFiniteType w δ₀, hδ₀.map_weylAction w, ?_, ?_⟩
  · rw [← hw]
    exact hp.map_weylAction w
  · have h1 := hg γ₀ hγ₀.mem
    have h2 := hg δ₀ hδ₀.mem
    rw [hw] at h1
    rw [← h1, ← h2]
    exact hP g _ _ h₀

end Group

end CFSG.ClassicalInvolution.ModelFacts
