module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Diag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7CombSymm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

open Matrix Finset

open scoped Classical

section Reindex

variable {G : Type} [Group G] [Fintype G] {L : Type} [Field L]

theorem sum_ker_mul {c : G → L} (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hcpow : ∀ x, c x ^ 3 = 1) {M : Type} [AddCommMonoid M] (F : G → M) (a : G) (ha : c a = 1) :
    ∑ x ∈ univ.filter (fun x => c x = 1), F (a * x) =
      ∑ x ∈ univ.filter (fun x => c x = 1), F x := by
  have hc1 : c 1 = 1 := char_one hcmul hcpow
  have hainv : c a⁻¹ = 1 := by
    have h := hcmul a⁻¹ a
    rw [inv_mul_cancel, hc1, ha, mul_one] at h
    exact h.symm
  apply Finset.sum_nbij' (fun x => a * x) (fun x => a⁻¹ * x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcmul, ha, one_mul, hx]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcmul, hainv, one_mul, hx]
  · intro x _
    exact inv_mul_cancel_left a x
  · intro x _
    exact mul_inv_cancel_left a x
  · intro x _
    rfl

theorem sum_ker_char {c : G → L} (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hcpow : ∀ x, c x ^ 3 = 1) {d : G → L} (hdmul : ∀ x y, d (x * y) = d x * d y) :
    ∑ x ∈ univ.filter (fun x => c x = 1), d x =
      if (∀ x, c x = 1 → d x = 1) then ((univ.filter (fun x => c x = 1)).card : L) else 0 := by
  split_ifs with htriv
  · rw [Finset.sum_congr rfl (fun x hx => htriv x (Finset.mem_filter.mp hx).2), Finset.sum_const,
      nsmul_eq_mul, mul_one]
  · push_neg at htriv
    obtain ⟨x0, hx0c, hx0d⟩ := htriv
    have hS : ∑ x ∈ univ.filter (fun x => c x = 1), d x = 0 := by
      have h1 := sum_ker_mul hcmul hcpow d x0 hx0c
      simp only [hdmul] at h1
      rw [← Finset.mul_sum] at h1
      have h2 : (d x0 - 1) * ∑ x ∈ univ.filter (fun x => c x = 1), d x = 0 := by
        rw [sub_mul, one_mul]
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd (sub_eq_zero.mp h3) hx0d
      · exact h3
    exact hS

end Reindex

section Proj

variable {K : Type} [Field K] {P : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K)}

abbrev mat (x : P) : Matrix (Fin 7) (Fin 7) K :=
  ((x : Matrix.SpecialLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)

theorem mat_mul (x y : P) : mat (P := P) (x * y) = mat (P := P) x * mat (P := P) y := by
  unfold mat
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]

theorem xL_eq {L : Type} [Field L] [Algebra K L] (x : P) :
    xL (L := L) (x : Matrix.SpecialLinearGroup (Fin 7) K) = (mat (P := P) x).map (algebraMap K L) :=
  rfl

theorem Dm_eq {L : Type} [Field L] [Algebra K L] (A : Matrix.GeneralLinearGroup (Fin 7) L)
    (x : Matrix.SpecialLinearGroup (Fin 7) K) :
    Dm A x = (A : Matrix (Fin 7) (Fin 7) L) * xL (L := L) x *
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) :=
  rfl

@[expose] noncomputable def projE (T : Finset P) : Matrix (Fin 7) (Fin 7) K :=
  ((T.card : K))⁻¹ • ∑ x ∈ T, mat (P := P) x

theorem projE_left {L : Type} [Field L] [Fintype P] (c : P → L)
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1) {f : P} (hf : c f = 1) :
    mat (P := P) f * projE (univ.filter fun x => c x = 1) =
      projE (univ.filter fun x => c x = 1) := by
  unfold projE
  rw [Matrix.mul_smul, Finset.mul_sum]
  congr 1
  have h := sum_ker_mul hcmul hcpow (fun y => mat (P := P) y) f hf
  simp only [mat_mul] at h
  simp only [← mat_mul] at h
  exact h

theorem projE_right {L : Type} [Field L] [Fintype P] (c : P → L)
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1) {f : P} (hf : c f = 1) :
    projE (univ.filter fun x => c x = 1) * mat (P := P) f =
      projE (univ.filter fun x => c x = 1) := by
  have hc1 : c 1 = 1 := char_one hcmul hcpow
  have hfinv : c f⁻¹ = 1 := by
    have h := hcmul f⁻¹ f
    rw [inv_mul_cancel, hc1, hf, mul_one] at h
    exact h.symm
  unfold projE
  rw [Matrix.smul_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_nbij' (fun x => x * f) (fun x => x * f⁻¹)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcmul, hx, hf, mul_one]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcmul, hx, hfinv, mul_one]
  · intro x _
    exact mul_inv_cancel_right x f
  · intro x _
    exact inv_mul_cancel_right x f
  · intro x _
    rw [mat_mul]

theorem projE_mul_self {L : Type} [Field L] [Fintype P] (c : P → L)
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (h9 : ((univ.filter fun x => c x = 1).card : K) ≠ 0) :
    projE (univ.filter fun x => c x = 1) * projE (univ.filter fun x => c x = 1) =
      projE (univ.filter fun x => c x = 1) := by
  set T := univ.filter fun x => c x = 1 with hT
  have hS : (∑ x ∈ T, mat (P := P) x) * (∑ x ∈ T, mat (P := P) x) =
      (T.card : K) • ∑ x ∈ T, mat (P := P) x := by
    rw [Finset.sum_mul]
    have hinner : ∀ x ∈ T, mat (P := P) x * (∑ y ∈ T, mat (P := P) y) =
        ∑ z ∈ T, mat (P := P) z := by
      intro x hx
      have hcx : c x = 1 := (Finset.mem_filter.mp hx).2
      rw [Finset.mul_sum]
      simp only [← mat_mul]
      exact sum_ker_mul hcmul hcpow (fun y => mat (P := P) y) x hcx
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  unfold projE
  rw [Matrix.smul_mul, Matrix.mul_smul, hS, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ h9, mul_one]

theorem rank_projE_map {L : Type} [Field L] [Algebra K L] [Fintype P]
    (A : Matrix.GeneralLinearGroup (Fin 7) L)
    (hA : ∀ x : P, ∀ i j, i ≠ j → Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i j = 0)
    (c : P → L) (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hcard : (univ.filter fun x => c x = 1).card = 9) (hk0 : ((9 : ℕ) : L) ≠ 0) :
    ((projE (univ.filter fun x => c x = 1)).map (algebraMap K L)).rank =
      (univ.filter fun i => ∀ x : P, c x = 1 → Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i i = 1).card := by
  set T := univ.filter fun x => c x = 1 with hT
  have hkT : ((T.card : ℕ) : L) = 9 := by
    rw [hT, hcard]
    norm_num
  have hmapE : (projE T).map (algebraMap K L) =
      ((T.card : L))⁻¹ • ∑ x ∈ T, (mat (P := P) x).map (algebraMap K L) := by
    ext i j
    simp [projE, Matrix.sum_apply, Matrix.smul_apply, map_sum]
  have hconj : A * ((projE T).map (algebraMap K L)) * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) L) :
      Matrix (Fin 7) (Fin 7) L) = Matrix.diagonal (fun i => ((T.card : L))⁻¹ *
        ∑ x ∈ T, Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i i) := by
    rw [hmapE, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
        Dm_eq, xL_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      rw [mul_eq_zero]
      right
      apply Finset.sum_eq_zero
      intro x _
      have := hA x i j hij
      rw [Dm_eq, xL_eq] at this
      exact this
  have hdmul : ∀ i (x y : P), Dm A ((x * y : P) : Matrix.SpecialLinearGroup (Fin 7) K) i i =
      Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i i *
        Dm A (y : Matrix.SpecialLinearGroup (Fin 7) K) i i := by
    intro i x y
    rw [Subgroup.coe_mul, Dm_mul]
    exact diag_mul_apply (hA x) (hA y) i
  rw [← rank_conj (A : Matrix (Fin 7) (Fin 7) L) _ _ (Units.mul_inv A), hconj,
    Matrix.rank_diagonal, Fintype.card_subtype]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  have hsum : ∑ x ∈ T, Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i i =
      if (∀ x, c x = 1 → Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i i = 1) then
        (T.card : L) else 0 :=
    sum_ker_char hcmul hcpow (fun x y => hdmul i x y)
  rw [hsum]
  have hk0' : (T.card : L) ≠ 0 := by
    rw [hcard]
    exact hk0
  split_ifs with htriv
  · rw [inv_mul_cancel₀ hk0']
    exact ⟨fun _ => htriv, fun _ => one_ne_zero⟩
  · rw [mul_zero]
    exact ⟨fun h => absurd rfl h, fun h => absurd h htriv⟩

end Proj

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

end
