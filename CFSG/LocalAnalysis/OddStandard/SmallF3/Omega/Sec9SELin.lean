module

public import CFSG.GH74.Filter.Small.Eigenbasis
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

private def sec9eEnd {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type} [Group E]
    (ρ : E →* (V ≃ₗ[ZMod 3] V)) : E →* Module.End (ZMod 3) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ

private lemma sec9eEnd_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type}
    [Group E] (ρ : E →* (V ≃ₗ[ZMod 3] V)) (g : E) :
    sec9eEnd ρ g = ((ρ g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) := rfl

private lemma sec9e_mul_comm {E : Type} [Group E] (hE : ∀ g : E, g * g = 1) :
    ∀ g h : E, g * h = h * g := by
  intro g h
  have hinv : ∀ x : E, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hE x)
  calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right (hE (g * h))).symm
    _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
    _ = h * g := by rw [hinv h, hinv g]

private lemma sec9eEnd_comm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type}
    [Group E] (ρ : E →* (V ≃ₗ[ZMod 3] V)) (hE : ∀ g : E, g * g = 1) :
    ∀ g h : E, Commute (sec9eEnd ρ g) (sec9eEnd ρ h) := by
  intro g h
  rw [commute_iff_eq, ← map_mul, ← map_mul, sec9e_mul_comm hE g h]

private lemma sec9eEnd_sq {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type}
    [Group E] (ρ : E →* (V ≃ₗ[ZMod 3] V)) (hE : ∀ g : E, g * g = 1) :
    ∀ g : E, sec9eEnd ρ g ^ 2 = 1 := by
  intro g
  have hg : g ^ 2 = 1 := by rw [pow_two, hE g]
  rw [← map_pow, hg, map_one]

private lemma sec9e_mu_eq_one_or_neg_one
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type} [Group E]
    {f : E →* Module.End (ZMod 3) V} {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {μ : E → Fin n → ZMod 3} (hb : ∀ g j, f g (b j) = μ g j • b j)
    (hsq : ∀ g, f g ^ 2 = 1) : ∀ g j, μ g j = 1 ∨ μ g j = -1 := by
  intro g j
  have h1 : (f g ^ 2) (b j) = b j := by rw [hsq g, Module.End.one_apply]
  rw [sq, Module.End.mul_apply, hb, map_smul, hb, smul_smul] at h1
  have h3 : (μ g j * μ g j - 1) • b j = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  have h4 : μ g j * μ g j = 1 :=
    sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  exact mul_self_eq_one_iff.1 h4

private lemma sec9e_mu_mul
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type} [Group E]
    {f : E →* Module.End (ZMod 3) V} {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {μ : E → Fin n → ZMod 3} (hb : ∀ g j, f g (b j) = μ g j • b j) :
    ∀ g h j, μ (g * h) j = μ g j * μ h j := by
  intro g h j
  have h1 : f (g * h) (b j) = μ (g * h) j • b j := hb (g * h) j
  have h2 : f (g * h) (b j) = (μ h j * μ g j) • b j := by
    rw [map_mul, Module.End.mul_apply, hb, map_smul, hb, smul_smul]
  have h3 : (μ (g * h) j - μ h j * μ g j) • b j = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  have h4 : μ (g * h) j = μ h j * μ g j :=
    sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  rw [h4, mul_comm]

private lemma sec9e_card
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type} [Group E]
    {f : E →* Module.End (ZMod 3) V} {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {μ : E → Fin n → ZMod 3} (hb : ∀ g j, f g (b j) = μ g j • b j)
    (hμ : ∀ g j, μ g j = 1 ∨ μ g j = -1) (g : E) :
    (Finset.univ.filter (fun j : Fin n => μ g j = -1)).card =
      Module.finrank (ZMod 3) (LinearMap.range (f g - 1)) := by
  have hsub : ∀ j : Fin n, (f g - 1) (b j) = (μ g j - 1) • b j := by
    intro j
    calc (f g - 1) (b j) = f g (b j) - (1 : Module.End (ZMod 3) V) (b j) := by
          rw [LinearMap.sub_apply]
      _ = μ g j • b j - b j := by rw [Module.End.one_apply, hb]
      _ = μ g j • b j - (1 : ZMod 3) • b j := by rw [one_smul]
      _ = (μ g j - 1) • b j := by rw [sub_smul]
  have hdiag : LinearMap.toMatrix b b (f g - 1) = Matrix.diagonal (fun j => μ g j - 1) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [LinearMap.toMatrix_apply, hsub]
    · simp [LinearMap.toMatrix_apply, hsub, hij]
  have hfilter : Finset.univ.filter (fun j : Fin n => μ g j - 1 ≠ 0) =
      Finset.univ.filter (fun j : Fin n => μ g j = -1) := by
    apply Finset.filter_congr
    intro j _
    rcases hμ g j with h | h <;> rw [h] <;> decide
  have hrank : (LinearMap.toMatrix b b (f g - 1)).rank =
      Module.finrank (ZMod 3) (LinearMap.range (f g - 1)) := by
    rw [Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix b b (f g - 1)) b b,
      Matrix.toLin_toMatrix]
  have hrank2 : (LinearMap.toMatrix b b (f g - 1)).rank =
      Fintype.card {j : Fin n // μ g j - 1 ≠ 0} := by
    rw [hdiag, Matrix.rank_diagonal]
  have hcard : (Finset.univ.filter (fun j : Fin n => μ g j = -1)).card =
      Fintype.card {j : Fin n // μ g j - 1 ≠ 0} := by
    rw [Fintype.card_subtype, ← hfilter]
  calc (Finset.univ.filter (fun j : Fin n => μ g j = -1)).card
      = Fintype.card {j : Fin n // μ g j - 1 ≠ 0} := hcard
    _ = (LinearMap.toMatrix b b (f g - 1)).rank := hrank2.symm
    _ = Module.finrank (ZMod 3) (LinearMap.range (f g - 1)) := hrank

private lemma sec9e_symmDiff
    {E : Type} [Group E] {n : ℕ} {μ : E → Fin n → ZMod 3}
    (hμ : ∀ g j, μ g j = 1 ∨ μ g j = -1)
    (hμmul : ∀ g h j, μ (g * h) j = μ g j * μ h j) (g h : E) :
    Finset.univ.filter (fun j : Fin n => μ (g * h) j = -1) =
      symmDiff (Finset.univ.filter (fun j : Fin n => μ g j = -1))
        (Finset.univ.filter (fun j : Fin n => μ h j = -1)) := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hμmul g h j]
  rcases hμ g j with hg | hg <;> rcases hμ h j with hh | hh <;> rw [hg, hh] <;> decide

private lemma sec9e_injective
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {E : Type} [Group E]
    (ρ : E →* (V ≃ₗ[ZMod 3] V)) (hρ : Function.Injective ρ)
    {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V} {f : E →* Module.End (ZMod 3) V}
    (hf : ∀ g, f g = ((ρ g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V))
    {μ : E → Fin n → ZMod 3} (hb : ∀ g j, f g (b j) = μ g j • b j)
    (hμ : ∀ g j, μ g j = 1 ∨ μ g j = -1) :
    Function.Injective (fun g : E => Finset.univ.filter (fun j : Fin n => μ g j = -1)) := by
  intro g h hgh
  have hmem : ∀ (x : E) (j : Fin n),
      j ∈ Finset.univ.filter (fun j : Fin n => μ x j = -1) ↔ μ x j = -1 := by
    intro x j
    simp
  have hgh' : Finset.univ.filter (fun j : Fin n => μ g j = -1) =
      Finset.univ.filter (fun j : Fin n => μ h j = -1) := hgh
  have hiff : ∀ j, μ g j = -1 ↔ μ h j = -1 := by
    intro j
    have h1 : j ∈ Finset.univ.filter (fun j : Fin n => μ g j = -1) ↔
        j ∈ Finset.univ.filter (fun j : Fin n => μ h j = -1) := by rw [hgh']
    rwa [hmem g j, hmem h j] at h1
  have hμeq : ∀ j, μ g j = μ h j := by
    intro j
    rcases hμ g j with hg | hg <;> rcases hμ h j with hh | hh
    · rw [hg, hh]
    · exact absurd ((hiff j).mpr hh) (by rw [hg]; decide)
    · exact absurd ((hiff j).mp hg) (by rw [hh]; decide)
    · rw [hg, hh]
  have hfh : f g = f h := b.ext fun j => by rw [hb, hb, hμeq j]
  have hfh' : ((ρ g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
      ((ρ h : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) := by
    rw [← hf g, ← hf h]
    exact hfh
  exact hρ (LinearEquiv.toLinearMap_injective hfh')

theorem sec9e_exists_subsets {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {E : Type} [Group E] [Finite E]
    (ρ : E →* (V ≃ₗ[ZMod 3] V)) (hρ : Function.Injective ρ) (hE : ∀ g : E, g * g = 1) :
    ∃ A : E → Finset (Fin (Module.finrank (ZMod 3) V)),
      Function.Injective A ∧ (∀ g h : E, A (g * h) = symmDiff (A g) (A h)) ∧
        ∀ g : E, (A g).card = Module.finrank (ZMod 3)
          (LinearMap.range (((ρ g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) - 1)) := by
  classical
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  let f : E →* Module.End (ZMod 3) V := sec9eEnd ρ
  have hf : ∀ g : E, f g = ((ρ g : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) :=
    fun g => sec9eEnd_apply ρ g
  have hcomm : ∀ i j : E, Commute (f i) (f j) := sec9eEnd_comm ρ hE
  have hsq : ∀ i : E, f i ^ 2 = 1 := sec9eEnd_sq ρ hE
  obtain ⟨b, μ, hb⟩ :=
    CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one h2 f hcomm hsq
  have hμ : ∀ g j, μ g j = 1 ∨ μ g j = -1 := sec9e_mu_eq_one_or_neg_one hb hsq
  have hμmul : ∀ g h j, μ (g * h) j = μ g j * μ h j := sec9e_mu_mul hb
  refine ⟨fun g => Finset.univ.filter (fun j => μ g j = -1), ?_, ?_, ?_⟩
  · exact sec9e_injective ρ hρ hf hb hμ
  · exact sec9e_symmDiff hμ hμmul
  · intro g
    rw [← hf g]
    exact sec9e_card hb hμ g

end CFSG.OddStandard.SmallF3.Omega
