module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type} [Field K] {d : ℕ}

theorem eq_one_of_smul_unipotent (hd : 0 < d) {N N' : Matrix (Fin d) (Fin d) K}
    (hN : N * N = 0) (hN' : N' * N' = 0) {s : K} (h : s • (1 + N') = 1 + N) : s = 1 := by
  have hNe : N = (s - 1) • (1 : Matrix (Fin d) (Fin d) K) + s • N' := by
    have h' : N = s • (1 + N') - 1 := by rw [h]; abel
    rw [h', smul_add, sub_smul, one_smul]
    abel
  have hE : (s - 1) ^ 2 • (1 : Matrix (Fin d) (Fin d) K) + (2 * s * (s - 1)) • N' = 0 := by
    have h1 : N * N = (s - 1) ^ 2 • (1 : Matrix (Fin d) (Fin d) K) + (2 * s * (s - 1)) • N' +
        (s * s) • (N' * N') := by
      rw [hNe]
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
      module
    rw [hN, hN', smul_zero, add_zero] at h1
    exact h1.symm
  have hE' : (s - 1) ^ 2 • N' = 0 := by
    have h1 := congrArg (· * N') hE
    simp only [add_mul, smul_mul_assoc, one_mul, hN', smul_zero, add_zero, zero_mul] at h1
    exact h1
  by_contra hs
  have hs' : (s - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs)
  have hN'0 : N' = 0 := (smul_eq_zero.mp hE').resolve_left hs'
  rw [hN'0, smul_zero, add_zero] at hE
  have h1 : (1 : Matrix (Fin d) (Fin d) K) = 0 := (smul_eq_zero.mp hE).resolve_left hs'
  have : (1 : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩ = 1 := Matrix.one_apply_eq _
  rw [h1] at this
  exact zero_ne_one this

variable {Q : QuadraticForm K (Fin d → K)}

theorem eq_of_projection_eq (hd : 0 < d) {M M' : matrixDerived Q}
    {N N' : Matrix (Fin d) (Fin d) K} (hM : ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + N)
    (hM' : ((M' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + N') (hN : N * N = 0)
    (hN' : N' * N' = 0)
    (h : matrixProjectiveProjection Q M = matrixProjectiveProjection Q M') : M = M' := by
  have h1 : M⁻¹ * M' ∈ matrixDerivedScalars Q := QuotientGroup.eq.mp h
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp h1
  have hc' : ((M' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (c : K) • ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    have h2 : (M' : GL (Fin d) K) = (M : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc]
      change (M' : GL (Fin d) K) = (M : GL (Fin d) K) * ((M : GL (Fin d) K)⁻¹ * M')
      group
    rw [h2, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  rw [hM, hM'] at hc'
  have hc1 : (c : K) = 1 := eq_one_of_smul_unipotent hd hN' hN hc'.symm
  apply Subtype.ext
  apply Units.ext
  rw [hM, hM'] at *
  rw [hc', hc1, one_smul]

theorem rootClass_injective (hd : 0 < d) {N : Matrix (Fin d) (Fin d) K} (hN2 : N * N = 0)
    (hN : N ≠ 0) (r : K → matrixDerived Q)
    (hr : ∀ c, (((r c : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N)
    {a b : K} (h : matrixProjectiveProjection Q (r a) = matrixProjectiveProjection Q (r b)) :
    a = b := by
  have hs : ∀ c : K, (c • N) * (c • N) = 0 := fun c => by
    rw [smul_mul_smul_comm, hN2, smul_zero]
  have h1 := eq_of_projection_eq hd (hr a) (hr b) (hs a) (hs b) h
  have h2 := congrArg (fun M : matrixDerived Q =>
    ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) h1
  simp only [hr] at h2
  have h3 : (a - b) • N = 0 := by
    rw [sub_smul, add_left_cancel h2, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hN)

theorem exists_root_action (hd : 0 < d) {N : Matrix (Fin d) (Fin d) K} (hN2 : N * N = 0)
    (hN : N ≠ 0) (r : K → matrixDerived Q)
    (hr : ∀ c, (((r c : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N)
    (g : similarityPairs Q)
    (hnorm : ∀ c, ∃ c', matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
      matrixProjectiveProjection Q (r c')) :
    ∃ l : K, ∀ c, matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
      matrixProjectiveProjection Q (r (l * g.val.right c)) := by
  set A := ((g.val.left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hA
  set Ai := (((g.val.left)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hAi
  set τ := g.val.right with hτ
  set N'' := A * N.map τ * Ai with hN''
  have hAAi : Ai * A = 1 := by
    rw [hA, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAAi' : A * Ai = 1 := by
    rw [hA, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hN''2 : N'' * N'' = 0 := by
    have hmap : N.map τ * N.map τ = 0 := by
      rw [← Matrix.map_mul, hN2, Matrix.map_zero _ (map_zero τ)]
    calc N'' * N'' = A * (N.map τ * (Ai * A) * N.map τ) * Ai := by
          rw [hN'']; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hAAi, Matrix.mul_one, hmap, Matrix.mul_zero, Matrix.zero_mul]
  have hm : ∀ c : K, (1 + c • N).map τ = 1 + τ c • N.map τ := by
    intro c
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hval : ∀ c, (((matrixDerivedConjugation Q g (r c) : matrixDerived Q) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = 1 + τ c • N'' := by
    intro c
    rw [matrixDerivedConjugation_val, Units.val_mul, Units.val_mul]
    change A * ((((r c : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map τ) *
      Ai = _
    rw [hr c, hm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAAi', Matrix.mul_smul,
      Matrix.smul_mul]
  have hs : ∀ c : K, (c • N) * (c • N) = 0 := fun c => by
    rw [smul_mul_smul_comm, hN2, smul_zero]
  have hs'' : ∀ c : K, (c • N'') * (c • N'') = 0 := fun c => by
    rw [smul_mul_smul_comm, hN''2, smul_zero]
  have hkey : ∀ c, ∃ c', τ c • N'' = c' • N ∧
      matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
        matrixProjectiveProjection Q (r c') := by
    intro c
    obtain ⟨c', hc'⟩ := hnorm c
    refine ⟨c', ?_, hc'⟩
    have h1 : matrixProjectiveProjection Q (matrixDerivedConjugation Q g (r c)) =
        matrixProjectiveProjection Q (r c') := by
      rw [← matrixProjectiveConjugation_mk]
      exact hc'
    have h2 := eq_of_projection_eq hd (hval c) (hr c') (hs'' (τ c)) (hs c') h1
    have h3 := congrArg (fun M : matrixDerived Q =>
      ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) h2
    simp only [hval, hr] at h3
    exact add_left_cancel h3
  obtain ⟨l, hl, -⟩ := hkey 1
  rw [map_one, one_smul] at hl
  refine ⟨l, fun c => ?_⟩
  obtain ⟨c', hc', hcc⟩ := hkey c
  rw [hcc]
  have h1 : c' • N = (l * τ c) • N := by
    rw [← hc', hl, smul_smul, mul_comm]
  have h2 : (c' - l * τ c) • N = 0 := by rw [sub_smul, h1, sub_self]
  rw [sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hN)]

theorem card_fixed_root_of_linear [Finite K] (hd : 0 < d) {N : Matrix (Fin d) (Fin d) K}
    (hN2 : N * N = 0) (hN : N ≠ 0) (r : K → matrixDerived Q)
    (hr : ∀ c, (((r c : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + c • N)
    (g : similarityPairs Q) (hτ : g.val.right = 1)
    (hnorm : ∀ c, ∃ c', matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
      matrixProjectiveProjection Q (r c')) :
    Nat.card {c : K // matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
        matrixProjectiveProjection Q (r c)} = 1 ∨
      Nat.card {c : K // matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
        matrixProjectiveProjection Q (r c)} = Nat.card K := by
  obtain ⟨l, hl⟩ := exists_root_action hd hN2 hN r hr g hnorm
  have hfix : ∀ c, matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (r c)) =
      matrixProjectiveProjection Q (r c) ↔ l * c = c := by
    intro c
    rw [hl c, hτ]
    constructor
    · exact rootClass_injective hd hN2 hN r hr
    · intro h
      change matrixProjectiveProjection Q (r (l * c)) = matrixProjectiveProjection Q (r c)
      rw [h]
  by_cases hl1 : l = 1
  · right
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun c => (hfix c).mpr (by rw [hl1, one_mul]))]
  · left
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, (hfix 0).mpr (by rw [mul_zero])⟩, fun x => Subtype.ext ?_⟩
    have h1 := (hfix x.1).mp x.2
    have h2 : (l - 1) * x.1 = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hl1)

end CFSG.ComponentClassification.Burgoyne.X10
