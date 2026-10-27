module

public import CFSG.ClassicalGroups.Orthogonal.SumSquares

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix
open scoped commutatorElement

private theorem trace_negCoordGL_pair {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {r s : ι} (hrs : r ≠ s) :
    ((negCoordGL (K := K) {r, s}) : Matrix ι ι K).trace =
      (Fintype.card ι : K) - 4 := by
  rw [negCoordGL, TauCeti.trace_diagGL]
  trans ∑ i, (if i ∈ ({r, s} : Finset ι) then (-1 : K) else 1)
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have hterm : ∀ i : ι, (if i ∈ ({r, s} : Finset ι) then (-1 : K) else 1) =
      (1 : K) + if i ∈ ({r, s} : Finset ι) then (-2 : K) else 0 := by
    intro i
    split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem_eq, Finset.sum_const,
    Finset.card_univ, Finset.card_pair hrs]
  simp
  ring

private theorem negCoordGL_singleton_mul_self {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (r : ι) :
    negCoordGL (K := K) {r} * negCoordGL (K := K) {r} = 1 := by
  simp only [negCoordGL]
  rw [← map_mul, ← map_one (TauCeti.diagGL (k := K) (ι := ι))]
  refine congrArg (TauCeti.diagGL (k := K) (ι := ι)) ?_
  funext i
  simp only [Pi.mul_apply, Pi.one_apply]
  split_ifs <;> simp

private theorem negCoordGL_singleton_mul_singleton {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] {r s : ι} (hrs : r ≠ s) :
    negCoordGL (K := K) {r} * negCoordGL (K := K) {s} = negCoordGL (K := K) {r, s} := by
  simp only [negCoordGL]
  rw [← map_mul]
  refine congrArg (TauCeti.diagGL (k := K) (ι := ι)) ?_
  funext i
  by_cases hir : i = r
  · subst hir
    simp [hrs]
  by_cases his : i = s
  · subst his
    simp [hir]
  · simp [hir, his]

private theorem swap_conj_negCoordGL_singleton {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {r s : ι} (hrs : r ≠ s) :
    TauCeti.permutationGL (k := K) (Equiv.swap r s) * negCoordGL (K := K) {r} *
        (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹ =
      negCoordGL (K := K) {s} := by
  have hswap : (Equiv.swap r s).symm = Equiv.swap r s := by
    simp
  have hfamily : (fun i => (if (Equiv.swap r s).symm i ∈ ({r} : Finset ι) then
        (-1 : Kˣ) else 1)) =
      fun i => if i ∈ ({s} : Finset ι) then (-1 : Kˣ) else 1 := by
    funext i
    rw [hswap]
    by_cases hir : i = r
    · subst hir
      simp [hrs, hrs.symm]
    by_cases his : i = s
    · subst his
      simp
    · simp [Equiv.swap_apply_of_ne_of_ne hir his, hir, his]
  simp only [negCoordGL]
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix
    (g := TauCeti.permutationGL (k := K) (Equiv.swap r s))
    (π := (Equiv.swap r s)⁻¹) (TauCeti.permutationGL_coe _),
    mul_inv_cancel_right]
  change TauCeti.diagGL (fun i => (if (Equiv.swap r s).symm i ∈ ({r} : Finset ι) then
      (-1 : Kˣ) else 1)) =
    TauCeti.diagGL (fun i => if i ∈ ({s} : Finset ι) then (-1 : Kˣ) else 1)
  rw [hfamily]

private theorem negCoordGL_pair_eq_commutator {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {r s : ι} (hrs : r ≠ s) :
    negCoordGL (K := K) {r, s} =
      ⁅negCoordGL (K := K) {r}, TauCeti.permutationGL (k := K) (Equiv.swap r s)⁆ := by
  have hDinv : (negCoordGL (K := K) {r})⁻¹ = negCoordGL (K := K) {r} :=
    inv_eq_of_mul_eq_one_right (negCoordGL_singleton_mul_self r)
  have hconj : TauCeti.permutationGL (k := K) (Equiv.swap r s) *
      (negCoordGL (K := K) {r})⁻¹ * (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹ =
        negCoordGL (K := K) {s} := by
    rw [hDinv]
    exact swap_conj_negCoordGL_singleton hrs
  rw [commutatorElement_def]
  symm
  calc
    negCoordGL (K := K) {r} * TauCeti.permutationGL (k := K) (Equiv.swap r s) *
        (negCoordGL (K := K) {r})⁻¹ * (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹ =
      negCoordGL (K := K) {r} *
        (TauCeti.permutationGL (k := K) (Equiv.swap r s) *
          (negCoordGL (K := K) {r})⁻¹ *
            (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹) := by group
    _ = negCoordGL (K := K) {r} * negCoordGL (K := K) {s} := by rw [hconj]
    _ = negCoordGL (K := K) {r, s} := negCoordGL_singleton_mul_singleton hrs

theorem negCoordGL_pair_mem_commutator {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {r s : ι} (hrs : r ≠ s) :
    negCoordGL (K := K) {r, s} ∈
      ⁅CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K)),
        CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K))⁆ := by
  rw [negCoordGL_pair_eq_commutator hrs]
  exact Subgroup.commutator_mem_commutator
    (negCoordGL_mem_orthogonalGroup_sumSqForm {r})
    (permutationGL_mem_orthogonalGroup_sumSqForm (Equiv.swap r s))

theorem permutationGL_commutatorElement_mem_commutator {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [Field K] (σ τ : Equiv.Perm ι) :
    TauCeti.permutationGL (k := K) ⁅σ, τ⁆ ∈
      ⁅CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K)),
        CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K))⁆ := by
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator
    (permutationGL_mem_orthogonalGroup_sumSqForm σ)
    (permutationGL_mem_orthogonalGroup_sumSqForm τ)

private theorem negCoordGL_mul_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (s : Finset ι) (g : GL ι K) (i j : ι) :
    ((negCoordGL (K := K) s * g : GL ι K) : Matrix ι ι K) i j =
      (if i ∈ s then (-1 : K) else 1) * (g : Matrix ι ι K) i j := by
  simp only [Units.val_mul, negCoordGL, TauCeti.diagGL_coe, Matrix.diagonal_mul]
  split_ifs <;> simp

private theorem mul_negCoordGL_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (s : Finset ι) (g : GL ι K) (i j : ι) :
    ((g * negCoordGL (K := K) s : GL ι K) : Matrix ι ι K) i j =
      (g : Matrix ι ι K) i j * (if j ∈ s then (-1 : K) else 1) := by
  simp only [Units.val_mul, negCoordGL, TauCeti.diagGL_coe, Matrix.mul_diagonal]
  split_ifs <;> simp

private theorem trace_eq_mul_trace_of_mul_scalar_eq {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] {g t : GL ι K} {u : Kˣ}
    (hu : g * t * Matrix.GeneralLinearGroup.scalar ι u = t * g) :
    (t : Matrix ι ι K).trace = ((u⁻¹ : Kˣ) : K) * (t : Matrix ι ι K).trace := by
  have hcyc : (((g * t * g⁻¹ : GL ι K)) : Matrix ι ι K).trace = (t : Matrix ι ι K).trace := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have h1 : (g * t * Matrix.GeneralLinearGroup.scalar ι u) * g⁻¹ = t := by
    rw [hu, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : (g * t * g⁻¹) * Matrix.GeneralLinearGroup.scalar ι u = t := by
    calc
      (g * t * g⁻¹) * Matrix.GeneralLinearGroup.scalar ι u =
          g * t * (g⁻¹ * Matrix.GeneralLinearGroup.scalar ι u) := by group
      _ = g * t * (Matrix.GeneralLinearGroup.scalar ι u * g⁻¹) := by
        rw [← Matrix.GeneralLinearGroup.scalar_commute u g⁻¹]
      _ = (g * t * Matrix.GeneralLinearGroup.scalar ι u) * g⁻¹ := by group
      _ = t := h1
  have hconj : g * t * g⁻¹ = t * (Matrix.GeneralLinearGroup.scalar ι u)⁻¹ := by
    calc
      g * t * g⁻¹ = ((g * t * g⁻¹) * Matrix.GeneralLinearGroup.scalar ι u) *
          (Matrix.GeneralLinearGroup.scalar ι u)⁻¹ := by group
      _ = t * (Matrix.GeneralLinearGroup.scalar ι u)⁻¹ := by rw [h2]
  calc
    (t : Matrix ι ι K).trace = (((g * t * g⁻¹ : GL ι K)) : Matrix ι ι K).trace := hcyc.symm
    _ = (((t * (Matrix.GeneralLinearGroup.scalar ι u)⁻¹ : GL ι K)) :
          Matrix ι ι K).trace := by rw [hconj]
    _ = ((u⁻¹ : Kˣ) : K) * (t : Matrix ι ι K).trace := by
      have hSinv : (Matrix.GeneralLinearGroup.scalar ι u)⁻¹ =
          Matrix.GeneralLinearGroup.scalar ι u⁻¹ :=
        (map_inv (Matrix.GeneralLinearGroup.scalar ι) u).symm
      simp only [Units.val_mul, hSinv, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply]
      rw [Matrix.trace_mul_comm (A := (t : Matrix ι ι K)),
        ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul]
      simp

private theorem commute_of_mk_mul_eq_mk_mul_of_trace_ne_zero {ι K : Type*} [Fintype ι]
    [DecidableEq ι]
    [Field K] {g t : GL ι K} (ht : (t : Matrix ι ι K).trace ≠ 0)
    (h : ProjGenLinGroup.mk g * ProjGenLinGroup.mk t =
      ProjGenLinGroup.mk t * ProjGenLinGroup.mk g) :
    g * t = t * g := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have htrace := trace_eq_mul_trace_of_mul_scalar_eq hu
  have ha : ((u⁻¹ : Kˣ) : K) = 1 :=
    mul_right_cancel₀ ht (by rw [one_mul]; exact htrace.symm)
  have hu1 : u⁻¹ = 1 := Units.ext ha
  have hueq : u = 1 := inv_eq_one.mp hu1
  rw [hueq] at hu
  simpa using hu

theorem apply_eq_zero_of_commute_negCoordGL {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (h2 : (2 : K) ≠ 0) (hcard : (Fintype.card ι : K) ≠ 4) (h3 : 3 ≤ Fintype.card ι)
    {g : GL ι K}
    (hc : ∀ r s : ι, r ≠ s → ProjGenLinGroup.mk g * ProjGenLinGroup.mk (negCoordGL {r, s}) =
      ProjGenLinGroup.mk (negCoordGL {r, s}) * ProjGenLinGroup.mk g)
    {i j : ι} (hij : i ≠ j) : (g : Matrix ι ι K) i j = 0 := by
  obtain ⟨k, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset ι)) (t := (Finset.univ : Finset ι)) (by
      rw [Finset.card_univ, Finset.card_pair hij]
      omega)
  have hk' : k ≠ i ∧ k ≠ j := by simpa using hk.2
  have hcomm : g * negCoordGL (K := K) {i, k} = negCoordGL (K := K) {i, k} * g :=
    commute_of_mk_mul_eq_mk_mul_of_trace_ne_zero
      (t := negCoordGL (K := K) {i, k})
      (by rw [trace_negCoordGL_pair hk'.1.symm]; exact sub_ne_zero.mpr hcard)
      (hc i k hk'.1.symm)
  have hentry : (g : Matrix ι ι K) i j = - (g : Matrix ι ι K) i j := by
    have h := congrFun (congrFun (congrArg (fun x : GL ι K => (x : Matrix ι ι K)) hcomm) i) j
    rw [mul_negCoordGL_apply, negCoordGL_mul_apply] at h
    simp only [Finset.mem_insert, Finset.mem_singleton, hij.symm, hk'.2.symm, hk'.1.symm] at h
    simpa using h
  have hxx : (g : Matrix ι ι K) i j + (g : Matrix ι ι K) i j = 0 := by
    nth_rewrite 2 [hentry]
    exact add_neg_cancel _
  have h2x : (2 : K) * (g : Matrix ι ι K) i j = 0 := by
    rw [two_mul]
    exact hxx
  exact (mul_eq_zero.mp h2x).resolve_left h2

end CFSG.ClassicalGroups.Orthogonal
