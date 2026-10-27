module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def chT (T g : GL (Fin 6) K) (i : Fin 6) : K :=
  ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i

theorem diag_entry_mul {M N : Matrix (Fin 6) (Fin 6) K}
    (hM : ∀ i j, i ≠ j → M i j = 0) (hN : ∀ i j, i ≠ j → N i j = 0) (i : Fin 6) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [hM i k (Ne.symm hk), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem conj_mul_eq (T g g' : GL (Fin 6) K) :
    T⁻¹ * (g * g') * T = (T⁻¹ * g * T) * (T⁻¹ * g' * T) := by
  group

theorem chT_mul (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    {g g' : GL (Fin 6) K} (hg : g ∈ P) (hg' : g' ∈ P) (i : Fin 6) :
    chT T (g * g') i = chT T g i * chT T g' i := by
  unfold chT
  rw [conj_mul_eq, Units.val_mul]
  exact diag_entry_mul (hdiag g hg) (hdiag g' hg') i

theorem chT_one (T : GL (Fin 6) K) (i : Fin 6) : chT T 1 i = 1 := by
  unfold chT
  rw [mul_one, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]

theorem chT_inv (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    {g : GL (Fin 6) K} (hg : g ∈ P) (i : Fin 6) :
    chT T g⁻¹ i = (chT T g i)⁻¹ := by
  have h1 := chT_mul P T hdiag (inv_mem hg) hg i
  rw [inv_mul_cancel, chT_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem chT_pow (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    {g : GL (Fin 6) K} (hg : g ∈ P) (i : Fin 6) (n : ℕ) :
    chT T (g ^ n) i = chT T g i ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, chT_one]
  | succ n ih =>
    rw [pow_succ, chT_mul P T hdiag (pow_mem hg n) hg i, ih, pow_succ]

theorem conj_eq_diagonal (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    {g : GL (Fin 6) K} (hg : g ∈ P) :
    ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal (chT T g) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [chT]
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact hdiag g hg i j hij

theorem eq_one_of_chT (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    {g : GL (Fin 6) K} (hg : g ∈ P) (h1 : ∀ i, chT T g i = 1) : g = 1 := by
  have hD : ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [conj_eq_diagonal P T hdiag hg]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [h1]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hD' : (T⁻¹ * g * T : GL (Fin 6) K) = 1 := Units.ext (by rw [hD, Units.val_one])
  calc g = T * (T⁻¹ * g * T) * T⁻¹ := by group
    _ = 1 := by rw [hD', mul_one, mul_inv_cancel]

theorem exists_T_diag [Finite K] (P : Subgroup (GL (Fin 6) K)) {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (hdet : ∀ g ∈ P, (g : Matrix (Fin 6) (Fin 6) K).det = 1)
    (hcomm : ∀ g ∈ P, ∀ g' ∈ P, g * g' = g' * g) (hpow : ∀ g ∈ P, g ^ 3 = 1) :
    ∃ T : GL (Fin 6) K, ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0 := by
  let toG : SpecialLinearGroup (Fin 6) K →* GL (Fin 6) K := Matrix.SpecialLinearGroup.toGL
  have toG_inj : Function.Injective toG := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun u : GL (Fin 6) K => (u : Matrix (Fin 6) (Fin 6) K)) hxy
    exact this
  let E₀ : Subgroup (SpecialLinearGroup (Fin 6) K) := P.comap toG
  have hcomm' : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
    intro x hx y hy
    apply toG_inj
    rw [map_mul, map_mul]
    exact hcomm _ hx _ hy
  have hpow' : ∀ x ∈ E₀, x ^ 3 = 1 := by
    intro x hx
    apply toG_inj
    rw [map_pow, map_one]
    exact hpow _ hx
  obtain ⟨A, hA⟩ :=
    CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ E₀ hcomm' hpow'
  refine ⟨A⁻¹, fun g hg i j hij => ?_⟩
  let x : SpecialLinearGroup (Fin 6) K := ⟨(g : Matrix (Fin 6) (Fin 6) K), hdet g hg⟩
  have hx : x ∈ E₀ := by
    show toG x ∈ P
    have : toG x = g := Units.ext rfl
    rw [this]
    exact hg
  have hAx := hA x hx i j hij
  rw [inv_inv, Units.val_mul, Units.val_mul]
  exact hAx

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
