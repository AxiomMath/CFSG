module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace TorusSU

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

section Spectral

variable {K : Type} [Field K] {σ : K ≃+* K} {n p : ℕ}

private theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin n → K) (y : Fin n → K) :
    herm σ (∑ i ∈ s, f i) y = ∑ i ∈ s, herm σ (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_left, ih]

private theorem herm_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → K) (f : ι → Fin n → K) :
    herm σ x (∑ i ∈ s, f i) = ∑ i ∈ s, herm σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right, ih]

private def perp {ι : Type*} (σ : K ≃+* K) (b : ι → Fin n → K) : Submodule K (Fin n → K) where
  carrier := {w | ∀ j, herm σ (b j) w = 0}
  add_mem' {x y} hx hy j := by rw [herm_add_right, hx j, hy j, add_zero]
  zero_mem' j := herm_zero_right σ _
  smul_mem' c x hx j := by rw [herm_smul_right, hx j, mul_zero]

private theorem mem_perp {ι : Type*} {b : ι → Fin n → K} {w : Fin n → K} :
    w ∈ perp σ b ↔ ∀ j, herm σ (b j) w = 0 := Iff.rfl

private def spec (ζ : K) (S : (Fin n → K) →ₗ[K] (Fin n → K)) (p i : ℕ) (w : Fin n → K) :
    Fin n → K :=
  (p : K)⁻¹ • ∑ j ∈ Finset.range p, ζ⁻¹ ^ (i * j) • (S ^ j) w

variable {ζ : K} {S : (Fin n → K) →ₗ[K] (Fin n → K)}

private theorem S_spec (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hSp : S ^ p = 1) (i : ℕ)
    (w : Fin n → K) : S (spec ζ S p i w) = ζ ^ i • spec ζ S p i w := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne'
  set T : ℕ → Fin n → K := fun m => ζ⁻¹ ^ (i * m) • (S ^ m) w with hT
  have h1 : ∀ j, ζ⁻¹ ^ (i * j) • S ((S ^ j) w) = ζ ^ i • T (j + 1) := by
    intro j
    have e1 : S ((S ^ j) w) = (S ^ (j + 1)) w := by rw [pow_succ', Module.End.mul_apply]
    have e2 : ζ ^ i * ζ⁻¹ ^ (i * (j + 1)) = ζ⁻¹ ^ (i * j) := by
      have h0 : ζ ^ i * ζ⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
      calc ζ ^ i * ζ⁻¹ ^ (i * (j + 1)) = (ζ ^ i * ζ⁻¹ ^ i) * ζ⁻¹ ^ (i * j) := by
            rw [mul_add, mul_one, pow_add]; ring
        _ = ζ⁻¹ ^ (i * j) := by rw [h0, one_mul]
    simp only [hT, e1, smul_smul, e2]
  have hTp : T p = T 0 := by
    have h2 : ζ⁻¹ ^ (i * p) = 1 := by
      rw [pow_mul', inv_pow, hζ.pow_eq_one, inv_one, one_pow]
    show ζ⁻¹ ^ (i * p) • (S ^ p) w = ζ⁻¹ ^ (i * 0) • (S ^ 0) w
    rw [h2, hSp]
    simp
  have hsum : ∑ j ∈ Finset.range p, T (j + 1) = ∑ j ∈ Finset.range p, T j := by
    have h2 := Finset.sum_range_succ' T p
    rw [Finset.sum_range_succ, hTp] at h2
    exact (add_right_cancel h2).symm
  have h3 : ∑ j ∈ Finset.range p, S (ζ⁻¹ ^ (i * j) • (S ^ j) w) =
      ζ ^ i • ∑ j ∈ Finset.range p, T j := by
    rw [← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, h1]
  unfold spec
  rw [map_smul, map_sum, h3, smul_comm]

private theorem sum_spec (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hp0 : (p : K) ≠ 0)
    (w : Fin n → K) : ∑ i ∈ Finset.range p, spec ζ S p i w = w := by
  have hgeom : ∀ j ∈ Finset.range p,
      ∑ i ∈ Finset.range p, ζ⁻¹ ^ (i * j) = if j = 0 then (p : K) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp_rw [pow_mul']
    split_ifs with h0
    · subst h0
      simp
    · have hx : ζ⁻¹ ^ j ≠ 1 := by
        intro h1
        rw [inv_pow, inv_eq_one] at h1
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (hζ.dvd_of_pow_eq_one j h1)
        omega
      have hxp : (ζ⁻¹ ^ j) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
      have h2 := geom_sum_mul (ζ⁻¹ ^ j) p
      rw [hxp, sub_self] at h2
      exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hx)
  calc ∑ i ∈ Finset.range p, spec ζ S p i w
      = (p : K)⁻¹ • ∑ j ∈ Finset.range p, (∑ i ∈ Finset.range p, ζ⁻¹ ^ (i * j)) • (S ^ j) w := by
        unfold spec
        rw [← Finset.smul_sum, Finset.sum_comm]
        simp_rw [Finset.sum_smul]
    _ = w := by
        rw [Finset.sum_congr rfl fun j hj => by rw [hgeom j hj], Finset.sum_eq_single 0]
        · simp [smul_smul, inv_mul_cancel₀ hp0]
        · intro j _ hj0
          simp [hj0]
        · intro h
          exact absurd (Finset.mem_range.mpr hp) h

private theorem spec_mem {W : Submodule K (Fin n → K)} (hW : ∀ x ∈ W, S x ∈ W) {w : Fin n → K}
    (hw : w ∈ W) (i : ℕ) : spec ζ S p i w ∈ W := by
  have hpow : ∀ j, (S ^ j) w ∈ W := by
    intro j
    induction j with
    | zero => simpa using hw
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hW _ ih
  exact W.smul_mem _ (W.sum_mem fun j _ => W.smul_mem _ (hpow j))

private theorem herm_eq_zero_of_eigen (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hσζ : σ ζ = ζ⁻¹)
    (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y) {x y : Fin n → K} {i i' : ℕ} (hi : i < p)
    (hi' : i' < p) (hne : i ≠ i') (hx : S x = ζ ^ i • x) (hy : S y = ζ ^ i' • y) :
    herm σ x y = 0 := by
  have h1 := hS x y
  rw [hx, hy, herm_smul_left, herm_smul_right, map_pow, hσζ] at h1
  by_contra h0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne'
  have h2 : ζ ^ i' * herm σ x y = ζ ^ i * herm σ x y := by
    have h3 : ζ ^ i * (ζ⁻¹ ^ i * (ζ ^ i' * herm σ x y)) = ζ ^ i * herm σ x y := by rw [h1]
    rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hζ0, one_pow, one_mul] at h3
  exact hne (hζ.pow_inj hi' hi (mul_right_cancel₀ h0 h2)).symm

private theorem exists_eigenvector_aniso (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hp0 : (p : K) ≠ 0)
    (hσζ : σ ζ = ζ⁻¹) (hSp : S ^ p = 1) (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y)
    (W : Submodule K (Fin n → K)) (hW : ∀ x ∈ W, S x ∈ W) {w : Fin n → K} (hw : w ∈ W)
    (hww : herm σ w w ≠ 0) : ∃ w' ∈ W, ∃ a : K, S w' = a • w' ∧ herm σ w' w' ≠ 0 := by
  have hsum := sum_spec (S := S) hζ hp hp0 w
  have hdiag : ∑ i ∈ Finset.range p, herm σ (spec ζ S p i w) (spec ζ S p i w) = herm σ w w := by
    conv_rhs => rw [← hsum]
    rw [herm_sum_left]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [herm_sum_right, Finset.sum_eq_single i]
    · intro i' hi' hne
      exact herm_eq_zero_of_eigen hζ hp hσζ hS (Finset.mem_range.mp hi) (Finset.mem_range.mp hi')
        (Ne.symm hne) (S_spec hζ hp hSp i w) (S_spec hζ hp hSp i' w)
    · intro h
      exact absurd hi h
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hdiag]; exact hww)
  exact ⟨spec ζ S p i w, spec_mem hW hw i, ζ ^ i, S_spec hζ hp hSp i w, hne⟩

private theorem exists_orthonormal_eigenbasis (hσ : IsUnitaryInvolution σ)
    (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (hp0 : (p : K) ≠ 0) (hσζ : σ ζ = ζ⁻¹)
    (hSp : S ^ p = 1) (hS : ∀ x y, herm σ (S x) (S y) = herm σ x y) :
    ∃ (b : Fin n → Fin n → K) (u : Fin n → K),
      (∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, S (b i) = u i • b i := by
  have key : ∀ k ≤ n, ∃ (b : Fin k → Fin n → K) (u : Fin k → K),
      (∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, S (b i) = u i • b i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨b, u, hb, hu⟩ := ih (by omega)
      have hu0 : ∀ i, σ (u i) ≠ 0 := by
        intro i h0
        have h1 := hS (b i) (b i)
        rw [hu i, herm_smul_left, herm_smul_right, hb i i, if_pos rfl, h0, zero_mul] at h1
        exact zero_ne_one h1
      have hWst : ∀ x ∈ perp σ b, S x ∈ perp σ b := by
        intro x hx j
        have h1 := hS (b j) x
        rw [hu j, herm_smul_left, mem_perp.mp hx j] at h1
        exact (mul_eq_zero.mp h1).resolve_left (hu0 j)
      let Q : (Fin n → K) →ₗ[K] (Fin n → K) :=
        LinearMap.id - ∑ i, (hermL σ (b i)).smulRight (b i)
      have hQy : ∀ y, Q y = y - ∑ i, herm σ (b i) y • b i := fun y => by simp [Q]
      have hQ1 : ∀ y j, herm σ (b j) (Q y) = 0 := by
        intro y j
        rw [hQy, herm_sub_right, herm_sum_right]
        simp [herm_smul_right, hb]
      obtain ⟨y, hy⟩ := exists_aniso_of_lt hσ (by omega : k < n) b Q
        (fun y => by
          rw [hQy, sub_sub_cancel]
          exact Submodule.sum_mem _ fun i _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
        hQ1
      obtain ⟨w, hwW, a, hSw, hww⟩ := exists_eigenvector_aniso hζ hp hp0 hσζ hSp hS (perp σ b)
        hWst (w := Q y) (mem_perp.mpr (hQ1 y)) hy
      obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hww
      have hbv : ∀ i, herm σ (b i) (c • w) = 0 := fun i =>
        mem_perp.mp ((perp σ b).smul_mem c hwW) i
      have hvb : ∀ i, herm σ (c • w) (b i) = 0 := fun i =>
        herm_eq_zero_comm σ hσ.invol (hbv i)
      have hSv : S (c • w) = a • c • w := by rw [map_smul, hSw, smul_comm]
      refine ⟨Fin.cons (c • w) b, Fin.cons a u, fun i j => ?_, fun i => ?_⟩
      · cases i using Fin.cases <;> cases j using Fin.cases <;>
          simp [hc, hbv, hvb, hb, (Fin.succ_ne_zero _).symm]
      · cases i using Fin.cases <;> simp [hSv, hu]
  exact key n le_rfl

end Spectral

section Matrices

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {P : Matrix (Fin n) (Fin n) K}

private def conjDiag (σ : K ≃+* K) (P : Matrix (Fin n) (Fin n) K) (t : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  P * diagonal t * conjTr σ P

private theorem conjTr_conjTr (hσ : ∀ c, σ (σ c) = c) (A : Matrix (Fin n) (Fin n) K) :
    conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hσ]

private theorem conjTr_diagonal (d : Fin n → K) :
    conjTr σ (diagonal d) = diagonal fun j => σ (d j) := by
  ext i j
  by_cases h : i = j <;> simp [conjTr, diagonal_apply, h, eq_comm]

private theorem mul_conjTr_self (hP : conjTr σ P * P = 1) : P * conjTr σ P = 1 :=
  mul_eq_one_comm.mp hP

private theorem conjDiag_mul (hP : conjTr σ P * P = 1) (t t' : Fin n → K) :
    conjDiag σ P t * conjDiag σ P t' = conjDiag σ P (t * t') := by
  unfold conjDiag
  calc P * diagonal t * conjTr σ P * (P * diagonal t' * conjTr σ P)
      = P * diagonal t * (conjTr σ P * P) * diagonal t' * conjTr σ P := by
        simp only [Matrix.mul_assoc]
    _ = P * (diagonal t * diagonal t') * conjTr σ P := by
        rw [hP, Matrix.mul_one, Matrix.mul_assoc P (diagonal t) (diagonal t')]
    _ = P * diagonal (t * t') * conjTr σ P := by rw [diagonal_mul_diagonal]; rfl

private theorem conjDiag_one (hP : conjTr σ P * P = 1) : conjDiag σ P 1 = 1 := by
  unfold conjDiag
  rw [Pi.one_def, diagonal_one, Matrix.mul_one, mul_conjTr_self hP]

private theorem conjTr_conjDiag (hσ : ∀ c, σ (σ c) = c) (t : Fin n → K) :
    conjTr σ (conjDiag σ P t) = conjDiag σ P fun j => σ (t j) := by
  unfold conjDiag
  rw [conjTr_mul, conjTr_mul, conjTr_diagonal, conjTr_conjTr hσ, Matrix.mul_assoc]

private theorem conjTr_conjDiag_mul_self (hσ : ∀ c, σ (σ c) = c) (hP : conjTr σ P * P = 1)
    {t : Fin n → K} (ht : ∀ j, σ (t j) * t j = 1) :
    conjTr σ (conjDiag σ P t) * conjDiag σ P t = 1 := by
  rw [conjTr_conjDiag hσ, conjDiag_mul hP]
  have : ((fun j => σ (t j)) * t) = 1 := funext ht
  rw [this, conjDiag_one hP]

private theorem det_conjDiag (hP : conjTr σ P * P = 1) (t : Fin n → K) :
    (conjDiag σ P t).det = ∏ j, t j := by
  unfold conjDiag
  rw [det_mul, det_mul, det_diagonal]
  have h := congrArg det (mul_conjTr_self hP)
  rw [det_mul, det_one] at h
  calc P.det * (∏ j, t j) * (conjTr σ P).det
      = (∏ j, t j) * (P.det * (conjTr σ P).det) := by ring
    _ = ∏ j, t j := by rw [h, mul_one]

private theorem diagonal_eq_conjDiag (hP : conjTr σ P * P = 1) (t : Fin n → K) :
    diagonal t = conjTr σ P * conjDiag σ P t * P := by
  unfold conjDiag
  calc diagonal t = (conjTr σ P * P) * diagonal t * (conjTr σ P * P) := by
        rw [hP, Matrix.one_mul, Matrix.mul_one]
    _ = conjTr σ P * (P * diagonal t * conjTr σ P) * P := by simp only [Matrix.mul_assoc]

private theorem commute_conjDiag (hP : conjTr σ P * P = 1) {s : Matrix (Fin n) (Fin n) K}
    {u : Fin n → K} (hsP : s * P = P * diagonal u) (t : Fin n → K) :
    s * conjDiag σ P t = conjDiag σ P t * s := by
  have h1 : conjTr σ P * s = diagonal u * conjTr σ P := by
    calc conjTr σ P * s = conjTr σ P * s * (P * conjTr σ P) := by
          rw [mul_conjTr_self hP, Matrix.mul_one]
      _ = conjTr σ P * (s * P) * conjTr σ P := by simp only [Matrix.mul_assoc]
      _ = conjTr σ P * (P * diagonal u) * conjTr σ P := by rw [hsP]
      _ = (conjTr σ P * P) * diagonal u * conjTr σ P := by simp only [Matrix.mul_assoc]
      _ = diagonal u * conjTr σ P := by rw [hP, Matrix.one_mul]
  unfold conjDiag
  calc s * (P * diagonal t * conjTr σ P) = (s * P) * diagonal t * conjTr σ P := by
        simp only [Matrix.mul_assoc]
    _ = P * (diagonal u * diagonal t) * conjTr σ P := by
        rw [hsP]; simp only [Matrix.mul_assoc]
    _ = P * (diagonal t * diagonal u) * conjTr σ P := by
        rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 3
        funext j
        exact mul_comm _ _
    _ = P * diagonal t * (diagonal u * conjTr σ P) := by simp only [Matrix.mul_assoc]
    _ = P * diagonal t * (conjTr σ P * s) := by rw [h1]
    _ = P * diagonal t * conjTr σ P * s := by simp only [Matrix.mul_assoc]

private def colMatrix (b : Fin n → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun r c => b c r

private theorem conjTr_colMatrix_mul_self {b : Fin n → Fin n → K}
    (hb : ∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) :
    conjTr σ (colMatrix b) * colMatrix b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply, ← hb i j, herm]
  simp [conjTr, colMatrix]

private theorem mul_colMatrix {s : Matrix (Fin n) (Fin n) K} {b : Fin n → Fin n → K} {u : Fin n → K}
    (hu : ∀ i, s *ᵥ b i = u i • b i) :
    s * colMatrix b = colMatrix b * diagonal u := by
  ext r c
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have := congrFun (hu c) r
  simpa [Matrix.mulVec, dotProduct, colMatrix, mul_comm] using this

end Matrices

section Torus

variable {K : Type} [Field K] {σ : K ≃+* K} {n p : ℕ} {ζ : K}

private theorem eq_one_of_conjDiag_eq_one {P : Matrix (Fin n) (Fin n) K} (hP : conjTr σ P * P = 1)
    {t : Fin n → K} (h : conjDiag σ P t = 1) (j : Fin n) : t j = 1 := by
  have hd : diagonal t = 1 := by
    rw [diagonal_eq_conjDiag hP, h, Matrix.mul_one, hP]
  have := congrFun (congrFun hd j) j
  simpa using this

private theorem exists_hom_conjDiag {P : Matrix (Fin n) (Fin n) K} (hσ : ∀ c, σ (σ c) = c)
    (hP : conjTr σ P * P = 1) {G : Type} [Group G] (T : G →* (Fin n → K))
    (hT : ∀ g j, σ (T g j) * T g j = 1) (hdet : ∀ g, ∏ j, T g j = 1) :
    ∃ F : G →* SUid σ n, ∀ g,
      (((F g : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = conjDiag σ P (T g) := by
  have hne : ∀ g, (conjDiag σ P (T g)).det ≠ 0 := fun g => by
    rw [det_conjDiag hP, hdet]
    exact one_ne_zero
  have hmem : ∀ g, Matrix.GeneralLinearGroup.mkOfDetNeZero (conjDiag σ P (T g)) (hne g) ∈
      SUid σ n := fun g =>
    ⟨by simp [det_conjDiag hP, hdet], by simpa using conjTr_conjDiag_mul_self hσ hP (hT g)⟩
  refine ⟨{ toFun := fun g => ⟨_, hmem g⟩, map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · apply Subtype.ext
    apply Units.ext
    simp [conjDiag_one hP]
  · intro g h
    apply Subtype.ext
    apply Units.ext
    simp [conjDiag_mul hP]

private theorem pow_mod_eq (hζ : IsPrimitiveRoot ζ p) (m : ℕ) : ζ ^ (m % p) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

private def charHom [NeZero p] (hζ : IsPrimitiveRoot ζ p) : Multiplicative (ZMod p) →* K where
  toFun a := ζ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, pow_mod_eq hζ, pow_add]

private theorem eq_one_of_charHom_eq_one [NeZero p] (hζ : IsPrimitiveRoot ζ p)
    {a : Multiplicative (ZMod p)} (h : charHom hζ a = 1) : a = 1 := by
  have h1 : ζ ^ (Multiplicative.toAdd a).val = 1 := h
  have h2 := hζ.dvd_of_pow_eq_one _ h1
  have h3 : (Multiplicative.toAdd a).val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt _)
  exact toAdd_eq_zero.mp ((ZMod.val_eq_zero _).mp h3)

private theorem norm_charHom [NeZero p] (hζ : IsPrimitiveRoot ζ p) (hσζ : σ ζ = ζ⁻¹)
    (a : Multiplicative (ZMod p)) : σ (charHom hζ a) * charHom hζ a = 1 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne p)
  show σ (ζ ^ (Multiplicative.toAdd a).val) * ζ ^ (Multiplicative.toAdd a).val = 1
  rw [map_pow, hσζ, ← mul_pow, inv_mul_cancel₀ hζ0, one_pow]

private def torusHom (χ : Multiplicative (ZMod p) →* K) (i0 i1 i2 i3 : Fin n) :
    (Fin 3 → Multiplicative (ZMod p)) →* (Fin n → K) where
  toFun x := Pi.mulSingle i0 (χ (x 0)) * Pi.mulSingle i1 (χ (x 1)) *
    Pi.mulSingle i2 (χ (x 2)) * Pi.mulSingle i3 (χ (x 0 * x 1 * x 2)⁻¹)
  map_one' := by simp
  map_mul' x y := by
    have e : (x 0 * y 0) * (x 1 * y 1) * (x 2 * y 2) = (x 0 * x 1 * x 2) * (y 0 * y 1 * y 2) := by
      rw [mul_mul_mul_comm (x 0) (y 0) (x 1) (y 1),
        mul_mul_mul_comm (x 0 * x 1) (y 0 * y 1) (x 2) (y 2)]
    simp only [Pi.mul_apply, map_mul, Pi.mulSingle_mul, e, mul_inv]
    ring

private theorem exists_torusHom_SUid (hσ : IsUnitaryInvolution σ) (hp : p.Prime) (hn : 5 ≤ n)
    (hζ : IsPrimitiveRoot ζ p) (hσζ : σ ζ = ζ⁻¹) (s : SUid σ n) (hs : s ^ p = 1) :
    ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* SUid σ n,
      Function.Injective F ∧ (∀ x, Commute (F x) s) ∧
      ∀ x, ((F x : SUid σ n) : GL (Fin n) K) ∈ CFSG.Open.StatedScalars (Fin n) K → F x = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : K) ≠ 0 := (hζ.neZero').out
  set sM : Matrix (Fin n) (Fin n) K := ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hsM
  have hsiso : conjTr σ sM * sM = 1 := s.2.2
  have hspow : sM ^ p = 1 := by
    have := congrArg (fun g : SUid σ n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hs
    simpa [hsM] using this
  have hSp : (Matrix.toLin' sM) ^ p = 1 := by
    rw [← Matrix.toLin'_pow, hspow, Matrix.toLin'_one]
    rfl
  have hS : ∀ x y, herm σ (Matrix.toLin' sM x) (Matrix.toLin' sM y) = herm σ x y := by
    intro x y
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_mulVec, hsiso, Matrix.one_mulVec]
  obtain ⟨b, u, hb, hu⟩ := exists_orthonormal_eigenbasis hσ hζ hp.pos hp0 hσζ hSp hS
  have hu' : ∀ i, sM *ᵥ b i = u i • b i := fun i => by
    rw [← Matrix.toLin'_apply]
    exact hu i
  have hP : conjTr σ (colMatrix b) * colMatrix b = 1 := conjTr_colMatrix_mul_self hb
  have hsP : sM * colMatrix b = colMatrix b * diagonal u := mul_colMatrix hu'
  obtain ⟨i0, i1, i2, i3, i4, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ :
      ∃ i0 i1 i2 i3 i4 : Fin n, i0 ≠ i1 ∧ i0 ≠ i2 ∧ i0 ≠ i3 ∧ i0 ≠ i4 ∧ i1 ≠ i2 ∧ i1 ≠ i3 ∧
        i1 ≠ i4 ∧ i2 ≠ i3 ∧ i2 ≠ i4 ∧ i3 ≠ i4 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩,
      by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  set T := torusHom (charHom hζ) i0 i1 i2 i3
  have hTx : ∀ x j, T x j = (Pi.mulSingle i0 (charHom hζ (x 0)) : Fin n → K) j *
      (Pi.mulSingle i1 (charHom hζ (x 1)) : Fin n → K) j *
        (Pi.mulSingle i2 (charHom hζ (x 2)) : Fin n → K) j *
          (Pi.mulSingle i3 (charHom hζ (x 0 * x 1 * x 2)⁻¹) : Fin n → K) j := fun x j => rfl
  have hms : ∀ (i j : Fin n) (a : K), σ a * a = 1 →
      σ ((Pi.mulSingle i a : Fin n → K) j) * (Pi.mulSingle i a : Fin n → K) j = 1 := by
    intro i j a ha
    by_cases h : j = i
    · subst h
      simpa using ha
    · simp [Pi.mulSingle_eq_of_ne h]
  have hmul : ∀ a b : K, σ a * a = 1 → σ b * b = 1 → σ (a * b) * (a * b) = 1 := by
    intro a b ha hb
    rw [map_mul]
    calc σ a * σ b * (a * b) = (σ a * a) * (σ b * b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  have hT : ∀ x j, σ (T x j) * T x j = 1 := by
    intro x j
    rw [hTx]
    exact hmul _ _ (hmul _ _ (hmul _ _ (hms _ _ _ (norm_charHom hζ hσζ _))
      (hms _ _ _ (norm_charHom hζ hσζ _))) (hms _ _ _ (norm_charHom hζ hσζ _)))
      (hms _ _ _ (norm_charHom hζ hσζ _))
  have hdet : ∀ x, ∏ j, T x j = 1 := by
    intro x
    simp only [hTx, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
    rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨F, hF⟩ := exists_hom_conjDiag hσ.invol hP T hT hdet
  have hone : ∀ (i j : Fin n) (a : K), j ≠ i → (Pi.mulSingle i a : Fin n → K) j = 1 :=
    fun i j a h => by simp [Pi.mulSingle_apply, h]
  have hT0 : ∀ x, T x i0 = charHom hζ (x 0) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i1 i0 _ h01, hone i2 i0 _ h02, hone i3 i0 _ h03]
    simp
  have hT1 : ∀ x, T x i1 = charHom hζ (x 1) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i0 i1 _ h01.symm, hone i2 i1 _ h12, hone i3 i1 _ h13]
    simp
  have hT2 : ∀ x, T x i2 = charHom hζ (x 2) := by
    intro x
    rw [hTx, Pi.mulSingle_eq_same, hone i0 i2 _ h02.symm, hone i1 i2 _ h12.symm,
      hone i3 i2 _ h23]
    simp
  have hT4 : ∀ x, T x i4 = 1 := by
    intro x
    rw [hTx, hone i0 i4 _ h04.symm, hone i1 i4 _ h14.symm, hone i2 i4 _ h24.symm,
      hone i3 i4 _ h34.symm]
    simp
  refine ⟨F, (injective_iff_map_eq_one F).mpr fun x hx => ?_, fun x => ?_, fun x hx => ?_⟩
  · have h1 : conjDiag σ (colMatrix b) (T x) = 1 := by
      rw [← hF x, hx]
      rfl
    have h2 := eq_one_of_conjDiag_eq_one hP h1
    have e0 : x 0 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT0 x]; exact h2 i0)
    have e1 : x 1 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT1 x]; exact h2 i1)
    have e2 : x 2 = 1 := eq_one_of_charHom_eq_one hζ (by rw [← hT2 x]; exact h2 i2)
    funext k
    fin_cases k
    exacts [e0, e1, e2]
  · show F x * s = s * F x
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hF x]
    exact (commute_conjDiag hP hsP _).symm
  · obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx
    have h1 : Matrix.scalar (Fin n) (c : K) = conjDiag σ (colMatrix b) (T x) := by
      have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
      simpa [hF x] using this
    have h2 : diagonal (T x) = diagonal fun _ => (c : K) := by
      rw [diagonal_eq_conjDiag hP, ← h1, Matrix.scalar_apply, ← smul_one_eq_diagonal,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP]
    have h3 : T x i4 = c := by
      have := congrFun (congrFun h2 i4) i4
      simpa using this
    have hc1 : c = 1 := Units.ext (by rw [← h3, hT4 x]; rfl)
    apply Subtype.ext
    apply Units.ext
    show (((F x : SUid σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [hF x, ← h1, hc1]
    simp

end Torus

end TorusSU

open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

theorem l212in_torusHom_su {p n r f : ℕ} [Fact r.Prime] (hp : p.Prime) (hn : 5 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K r] (hK : Nat.card K = (r ^ f) ^ 2)
    (hpq : p ∣ r ^ f + 1) (s : CFSG.Open.StatedSU n (r ^ f) K) (hs : s ^ p = 1) :
    ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* CFSG.Open.StatedSU n (r ^ f) K,
      Function.Injective F ∧ (∀ x, Commute (F x) s) ∧
      ∀ x, ((F x : CFSG.Open.StatedSU n (r ^ f) K) : GL (Fin n) K) ∈
        CFSG.Open.StatedScalars (Fin n) K → F x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hq : 1 < r ^ f := one_lt_pow_of_card hK
  have hcard : p ∣ Nat.card Kˣ := by
    rw [card_units_of_card hK, sq_sub_one_eq _ hq.le]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζu, hζu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p hcard
  have hζ : IsPrimitiveRoot (ζu : K) p :=
    IsPrimitiveRoot.coe_units_iff.mpr (hζu ▸ IsPrimitiveRoot.orderOf ζu)
  have hσζ : unitaryInvolution K r f (ζu : K) = (ζu : K)⁻¹ := by
    rw [unitaryInvolution_apply]
    have h1 : ζu ^ (r ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hζu]; exact hpq)
    have h2 : ζu ^ (r ^ f) = ζu⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
    have h3 := congrArg (fun u : Kˣ => (u : K)) h2
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using h3
  have main : ∀ H : Subgroup (GL (Fin n) K), H = SUid (unitaryInvolution K r f) n →
      ∀ s : H, s ^ p = 1 → ∃ F : (Fin 3 → Multiplicative (ZMod p)) →* H,
        Function.Injective F ∧ (∀ x, Commute (F x) s) ∧
        ∀ x, ((F x : H) : GL (Fin n) K) ∈ CFSG.Open.StatedScalars (Fin n) K → F x = 1 := by
    intro H hH
    subst hH
    exact fun s hs => TorusSU.exists_torusHom_SUid hσ hp hn hζ hσζ s hs
  exact main _ (SUid_eq_statedSU hK n).symm s hs

end CFSG.LocalAnalysis.RankFourTheoremC
