module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sec9gd_sign_mul_symmDiff {n : ℕ} (T₁ T₂ : Finset (Fin n)) (i : Fin n) :
    ((if i ∈ T₂ then (-1 : ZMod 3) else 1) * (if i ∈ T₁ then (-1 : ZMod 3) else 1)) =
      (if i ∈ symmDiff T₁ T₂ then (-1 : ZMod 3) else 1) := by
  by_cases h1 : i ∈ T₁ <;> by_cases h2 : i ∈ T₂ <;>
    simp [Finset.mem_symmDiff, h1, h2]

private lemma sec9gd_finrank_range_sub_one {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V}
    {g : V ≃ₗ[ZMod 3] V} {T : Finset (Fin n)}
    (h : ∀ i, g (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i) :
    Module.finrank (ZMod 3) (LinearMap.range ((g : V →ₗ[ZMod 3] V) - 1)) = T.card := by
  classical
  let μ : Fin n → ZMod 3 := fun j => if j ∈ T then (-1 : ZMod 3) else 1
  have hb : ∀ j, (g : V →ₗ[ZMod 3] V) (b j) = μ j • b j := by
    intro j
    change (g : V → V) (b j) = μ j • b j
    rw [h j]
  have hμ : ∀ j, μ j = 1 ∨ μ j = -1 := by
    intro j
    by_cases hj : j ∈ T <;> simp [μ, hj]
  have hsub : ∀ j : Fin n, (((g : V →ₗ[ZMod 3] V) - 1) (b j)) = (μ j - 1) • b j := by
    intro j
    calc (((g : V →ₗ[ZMod 3] V) - 1) (b j))
        = (g : V →ₗ[ZMod 3] V) (b j) - (1 : Module.End (ZMod 3) V) (b j) := by
          rw [LinearMap.sub_apply]
      _ = μ j • b j - b j := by rw [Module.End.one_apply, hb]
      _ = μ j • b j - (1 : ZMod 3) • b j := by rw [one_smul]
      _ = (μ j - 1) • b j := by rw [sub_smul]
  have hdiag : LinearMap.toMatrix b b ((g : V →ₗ[ZMod 3] V) - 1) =
      Matrix.diagonal (fun j => μ j - 1) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [LinearMap.toMatrix_apply, hsub]
    · simp [LinearMap.toMatrix_apply, hsub, hij]
  have hfilter : Finset.univ.filter (fun j : Fin n => μ j - 1 ≠ 0) =
      Finset.univ.filter (fun j : Fin n => μ j = -1) := by
    apply Finset.filter_congr
    intro j _
    rcases hμ j with h | h <;> rw [h] <;> decide
  have hfilterT : Finset.univ.filter (fun j : Fin n => μ j = -1) = T := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      by_contra hT
      simp only [μ, hT, if_false] at hj
      exact (by decide : (1 : ZMod 3) ≠ -1) hj
    · intro hT
      simp [μ, hT]
  have hrank : (LinearMap.toMatrix b b ((g : V →ₗ[ZMod 3] V) - 1)).rank =
      Module.finrank (ZMod 3) (LinearMap.range ((g : V →ₗ[ZMod 3] V) - 1)) := by
    rw [Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix b b ((g : V →ₗ[ZMod 3] V) - 1)) b b,
      Matrix.toLin_toMatrix]
  have hrank2 : (LinearMap.toMatrix b b ((g : V →ₗ[ZMod 3] V) - 1)).rank =
      Fintype.card {j : Fin n // μ j - 1 ≠ 0} := by
    rw [hdiag, Matrix.rank_diagonal]
  have hcard : (Finset.univ.filter (fun j : Fin n => μ j = -1)).card =
      Fintype.card {j : Fin n // μ j - 1 ≠ 0} := by
    rw [Fintype.card_subtype, ← hfilter]
  calc Module.finrank (ZMod 3) (LinearMap.range ((g : V →ₗ[ZMod 3] V) - 1))
      = (LinearMap.toMatrix b b ((g : V →ₗ[ZMod 3] V) - 1)).rank := hrank.symm
    _ = Fintype.card {j : Fin n // μ j - 1 ≠ 0} := hrank2
    _ = (Finset.univ.filter (fun j : Fin n => μ j = -1)).card := hcard.symm
    _ = T.card := by rw [hfilterT]

theorem sec9g_mul_self_diag {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V} {g : OGroup Q}
    {T : Finset (Fin n)}
    (h : ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i) :
    g * g = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  apply b.ext'
  intro i
  rw [LinearEquiv.mul_apply, h i, map_smul, h i, smul_smul]
  by_cases hi : i ∈ T <;> simp [hi]

theorem sec9g_invDim_diag {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V} {g : OGroup Q}
    {T : Finset (Fin n)}
    (h : ∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ T then (-1 : ZMod 3) else 1) • b i) :
    invDim g = T.card := by
  show Module.finrank (ZMod 3) (LinearMap.range ((g : V →ₗ[ZMod 3] V) - 1)) = T.card
  exact sec9gd_finrank_range_sub_one h

theorem sec9g_mul_diag {n : ℕ} {b : Module.Basis (Fin n) (ZMod 3) V} {g₁ g₂ : OGroup Q}
    {T₁ T₂ : Finset (Fin n)}
    (h₁ : ∀ i, (g₁ : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ T₁ then (-1 : ZMod 3) else 1) • b i)
    (h₂ : ∀ i, (g₂ : V ≃ₗ[ZMod 3] V) (b i) = (if i ∈ T₂ then (-1 : ZMod 3) else 1) • b i) :
    ∀ i, ((g₁ * g₂ : OGroup Q) : V ≃ₗ[ZMod 3] V) (b i) =
      (if i ∈ symmDiff T₁ T₂ then (-1 : ZMod 3) else 1) • b i := by
  intro i
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h₂ i, map_smul, h₁ i, smul_smul]
  rw [sec9gd_sign_mul_symmDiff]

end CFSG.OddStandard.SmallF3.Omega
