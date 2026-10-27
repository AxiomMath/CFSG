module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Rank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Block
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Lower

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (two_le_pRank_statedProj)

section Block
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def pairIncl (e : Fin 2 → Fin 2 → ι) (b : Fin 2) : Matrix ι (Fin 2) K :=
  Matrix.of fun i k => if i = e b k then 1 else 0

@[expose] def blk (e : Fin 2 → Fin 2 → ι) (b : Fin 2) (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix ι ι K :=
  1 + (pairIncl e b : Matrix ι (Fin 2) K) * (M - 1) * (pairIncl e b : Matrix ι (Fin 2) K)ᵀ

variable {e : Fin 2 → Fin 2 → ι}

theorem pairIncl_transpose_mul
    (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b c : Fin 2) :
    (pairIncl e b : Matrix ι (Fin 2) K)ᵀ * (pairIncl e c : Matrix ι (Fin 2) K) =
      (if b = c then 1 else 0 : Matrix (Fin 2) (Fin 2) K) := by
  ext k l
  simp only [Matrix.mul_apply, pairIncl, Matrix.transpose_apply, Matrix.of_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (e b k)]
  simp only [Finset.mem_univ, ite_true]
  by_cases hbc : b = c <;> by_cases hkl : k = l
  · subst hbc; subst hkl; simp
  · subst hbc; have : ¬ (e b k = e b l) := fun h => hkl (he _ _ _ _ h).2
    simp [this, hkl]
  · have : ¬ (e b k = e c l) := fun h => hbc (he _ _ _ _ h).1
    simp [this, hbc]
  · have : ¬ (e b k = e c l) := fun h => hbc (he _ _ _ _ h).1
    simp [this, hbc]

theorem pairIncl_transpose_mul_self (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2) :
    (pairIncl e b : Matrix ι (Fin 2) K)ᵀ * (pairIncl e b : Matrix ι (Fin 2) K) = 1 := by
  rw [pairIncl_transpose_mul he]; simp

theorem pairIncl_transpose_mul_ne (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 2}
    (h : b ≠ c) :
    (pairIncl e b : Matrix ι (Fin 2) K)ᵀ * (pairIncl e c : Matrix ι (Fin 2) K) = 0 := by
  rw [pairIncl_transpose_mul he]; simp [h]

omit [Fintype ι] in
theorem blk_one (b : Fin 2) : blk e b (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by simp [blk]

theorem blk_mul (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2)
    (M N : Matrix (Fin 2) (Fin 2) K) : blk e b M * blk e b N = blk e b (M * N) := by
  set P : Matrix ι (Fin 2) K := pairIncl e b with hPdef
  have hP : Pᵀ * P = 1 := pairIncl_transpose_mul_self he b
  have h : P * (M - 1) * Pᵀ * (P * (N - 1) * Pᵀ) = P * ((M - 1) * (N - 1)) * Pᵀ := by
    calc P * (M - 1) * Pᵀ * (P * (N - 1) * Pᵀ)
        = P * (M - 1) * (Pᵀ * P) * (N - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have hMN : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold blk
  rw [← hPdef, hMN]
  have e1 : ∀ X Y : Matrix ι ι K, (1 + X) * (1 + Y) = 1 + X + Y + X * Y := fun X Y => by
    noncomm_ring
  rw [e1, h]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel


theorem blk_pow (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2)
    (M : Matrix (Fin 2) (Fin 2) K) (k : ℕ) : blk e b M ^ k = blk e b (M ^ k) := by
  induction k with
  | zero => simp [blk_one]
  | succ k ih => rw [pow_succ, ih, blk_mul he, pow_succ]

theorem blk_det (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2)
    (M : Matrix (Fin 2) (Fin 2) K) : (blk e b M).det = M.det := by
  set P : Matrix ι (Fin 2) K := pairIncl e b with hPdef
  have hP : Pᵀ * P = 1 := pairIncl_transpose_mul_self he b
  have : blk e b M = 1 + (P * (M - 1)) * Pᵀ := rfl
  rw [this, Matrix.det_one_add_mul_comm]
  have h2 : Pᵀ * (P * (M - 1)) = M - 1 := by rw [← Matrix.mul_assoc, hP, Matrix.one_mul]
  rw [h2]; simp

theorem blk_comm (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 2} (h : b ≠ c)
    (M N : Matrix (Fin 2) (Fin 2) K) : blk e b M * blk e c N = blk e c N * blk e b M := by
  set P : Matrix ι (Fin 2) K := pairIncl e b with hPdef
  set Q : Matrix ι (Fin 2) K := pairIncl e c with hQdef
  have h1 : Pᵀ * Q = 0 := pairIncl_transpose_mul_ne he h
  have h2 : Qᵀ * P = 0 := pairIncl_transpose_mul_ne he h.symm
  have e1 : ∀ X Y : Matrix ι ι K, (1 + X) * (1 + Y) = 1 + X + Y + X * Y := fun X Y => by
    noncomm_ring
  unfold blk
  rw [← hPdef, ← hQdef, e1, e1]
  have h3 : P * (M - 1) * Pᵀ * (Q * (N - 1) * Qᵀ) = 0 := by
    calc _ = P * (M - 1) * (Pᵀ * Q) * (N - 1) * Qᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1]; simp
  have h4 : Q * (N - 1) * Qᵀ * (P * (M - 1) * Pᵀ) = 0 := by
    calc _ = Q * (N - 1) * (Qᵀ * P) * (M - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h2]; simp
  rw [h3, h4]
  abel


omit [Fintype ι] in
theorem pairIncl_map (φ : K →+* K) (b : Fin 2) :
    (pairIncl e b : Matrix ι (Fin 2) K).map φ = pairIncl e b := by
  ext i k; simp only [pairIncl, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

theorem blk_map_transpose (φ : K →+* K) (b : Fin 2) (M : Matrix (Fin 2) (Fin 2) K) :
    ((blk e b M).map φ)ᵀ = blk e b ((M.map φ)ᵀ) := by
  unfold blk
  have h1 : ((1 : Matrix ι ι K).map φ) = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
  have h2 : ((1 : Matrix (Fin 2) (Fin 2) K).map φ) = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
  have h3 : ((M - 1).map φ) = M.map φ - 1 := by rw [Matrix.map_sub _ (map_sub φ), h2]
  have hm1 : ∀ (A : Matrix ι (Fin 2) K) (B : Matrix (Fin 2) (Fin 2) K) (C : Matrix (Fin 2) ι K),
      (A * B * C).map φ = A.map φ * B.map φ * C.map φ := fun A B C => by
    rw [Matrix.map_mul, Matrix.map_mul]
  have hPt : (pairIncl e b : Matrix ι (Fin 2) K)ᵀ.map φ = (pairIncl e b)ᵀ := by
    rw [Matrix.transpose_map, pairIncl_map]
  rw [Matrix.map_add _ (map_add φ), h1, hm1, h3, hPt, pairIncl_map, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_sub, Matrix.transpose_one]
  simp only [Matrix.mul_assoc]


theorem blk_apply_same (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2)
    (M : Matrix (Fin 2) (Fin 2) K) (k l : Fin 2) : blk e b M (e b k) (e b l) = M k l := by
  have h01 : e b 0 ≠ e b 1 := fun h => by simpa using (he _ _ _ _ h).2
  have h10 : e b 1 ≠ e b 0 := h01.symm
  fin_cases k <;> fin_cases l <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_two, pairIncl, Matrix.one_apply, h01, h10]

theorem blk_apply_other (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 2} (h : c ≠ b)
    (M : Matrix (Fin 2) (Fin 2) K) (k : Fin 2) (j : ι) :
    blk e b M (e c k) j = (1 : Matrix ι ι K) (e c k) j := by
  have h0 : e c k ≠ e b 0 := fun h' => h (he _ _ _ _ h').1
  have h1 : e c k ≠ e b 1 := fun h' => h (he _ _ _ _ h').1
  simp [blk, Matrix.mul_apply, Fin.sum_univ_two, pairIncl, h0, h1]

theorem mul_apply_of_row {A B : Matrix ι ι K} {i : ι} (h : ∀ j, A i j = (1 : Matrix ι ι K) i j)
    (j : ι) : (A * B) i j = B i j := by
  simp [Matrix.mul_apply, h, Matrix.one_apply]


@[expose] def blkGL (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) : GL ι K :=
  ⟨blk e b M, blk e b (M * M), by rw [blk_mul he, ← pow_three, h3, blk_one],
    by rw [blk_mul he, ← pow_three', h3, blk_one]⟩

theorem coe_blkGL (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) :
    ((blkGL he b M h3 : GL ι K) : Matrix ι ι K) = blk e b M := rfl

theorem blkGL_pow_three (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) (b : Fin 2)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) : blkGL he b M h3 ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_blkGL, blk_pow he, h3, blk_one]; rfl

theorem blkGL_commute (he : ∀ b k c l, e b k = e c l → b = c ∧ k = l) {b c : Fin 2} (h : b ≠ c)
    (M : Matrix (Fin 2) (Fin 2) K) (h3 : M ^ 3 = 1) :
    Commute (blkGL he b M h3 : GL ι K) (blkGL he c M h3) :=
  Units.ext (by
    simp only [Units.val_mul, coe_blkGL]; exact blk_comm he h M M)

theorem scalar_apply_ne {u : Kˣ} {i j : ι} (h : i ≠ j) :
    ((Matrix.GeneralLinearGroup.scalar ι u : GL ι K) : Matrix ι ι K) i j = 0 := by
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, h]


end Block

section Two

variable {K : Type} [Field K]

theorem two_le_pRank_of_su2_cube [Finite K] {n q : ℕ} (hn : 4 ≤ n) (φ : K →+* K)
    (hφ : ∀ x, φ x = x ^ q) (M : Matrix (Fin 2) (Fin 2) K) (hM1 : (M.map φ)ᵀ * M = 1)
    (hM3 : M ^ 3 = 1) (hMdet : M.det = 1) (hMs : M 0 1 ≠ 0 ∨ M 0 0 ≠ M 1 1) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let c : Fin 2 → Fin 2 → Fin n := fun b k => ⟨2 * b.val + k.val, by omega⟩
  have hc : ∀ b k b' k', c b k = c b' k' → b = b' ∧ k = k' := fun b k b' k' h => by
    have := congrArg Fin.val h
    simp only [c] at this
    have hb := b.isLt; have hk := k.isLt; have hb' := b'.isLt; have hk' := k'.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  have hunit : ∀ b : Fin 2, blkGL hc b M hM3 ∈ StatedSU n q K := fun b => by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · show (blk c b M).det = 1
      rw [blk_det hc, hMdet]
    · show ((blk c b M).map (· ^ q))ᵀ * blk c b M = 1
      have : (fun x : K => x ^ q) = ⇑φ := funext fun x => (hφ x).symm
      rw [this, blk_map_transpose, blk_mul hc, hM1, blk_one]
  have hnot : ∀ u : K, M 0 1 = 0 → M 0 0 = u → M 1 1 = u → False := fun u h1 h0 h1' =>
    hMs.elim (fun h => h h1) (fun h => h (h0.trans h1'.symm))
  have hsc : ∀ (u : Kˣ) (i : Fin n), ((Matrix.GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i i = u := fun u i => by
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have hne : ∀ b k l, k ≠ l → c b k ≠ c b l := fun b k l h h' => h (hc _ _ _ _ h').2
  refine two_le_pRank_statedProj (hunit 0) (hunit 1) (blkGL_pow_three hc _ _ _)
    (blkGL_pow_three hc _ _ _) (blkGL_commute hc (by decide) M hM3) ?_ ?_
  · rintro ⟨u, hu⟩
    have e01 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 0 0) (c 0 1)) hu
    have e00 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 0 0) (c 0 0)) hu
    have e11 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 0 1) (c 0 1)) hu
    simp only [coe_blkGL, blk_apply_same hc] at e01 e00 e11
    rw [scalar_apply_ne (hne 0 0 1 (by decide))] at e01
    rw [hsc] at e00 e11
    exact hnot u e01.symm e00.symm e11.symm
  · rintro m _ ⟨u, rfl⟩ h
    have e01 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 1 0) (c 1 1)) h
    have e00 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 1 0) (c 1 0)) h
    have e11 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) (c 1 1) (c 1 1)) h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_blkGL, blk_pow hc] at e01 e00 e11
    rw [mul_apply_of_row (fun j => blk_apply_other hc (by decide) _ _ _),
      scalar_apply_ne (hne 1 0 1 (by decide)), blk_apply_same hc] at e01
    rw [mul_apply_of_row (fun j => blk_apply_other hc (by decide) _ _ _), hsc,
      blk_apply_same hc] at e00 e11
    exact hnot u e01.symm e00.symm e11.symm

end Two

section Odd

variable {K : Type} [Field K] [Fintype K]

theorem exists_norm_eq (φ : K →+* K) (q : ℕ) (hφ : ∀ x, φ x = x ^ q) (hq2 : 2 ≤ q) (g : Kˣ)
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) (hord : orderOf g = q ^ 2 - 1) (y : K)
    (hy : φ y = y) : ∃ b : K, b * φ b = y := by
  by_cases hy0 : y = 0
  · exact ⟨0, by simp [hy0]⟩
  obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.2 (hg (Units.mk0 y hy0))
  have hjy : (g : K) ^ j = y := by simpa using congrArg Units.val hj
  have hqy : y ^ q = y := by rw [← hφ]; exact hy
  have hsub : q - 1 + 1 = q := by omega
  have h1 : g ^ (j * (q - 1)) = 1 := by
    have h0 : (g : K) ^ j ≠ 0 := by rw [hjy]; exact hy0
    have hGq : (g : K) ^ (j * q) = (g : K) ^ j := by rw [pow_mul, hjy]; exact hqy
    have hjq : j + j * (q - 1) = j * q := by
      calc j + j * (q - 1) = j * 1 + j * (q - 1) := by ring
        _ = j * (1 + (q - 1)) := by ring
        _ = j * q := by congr 1; omega
    have h2 : (g : K) ^ j * (g : K) ^ (j * (q - 1)) = (g : K) ^ j * 1 := by
      rw [← pow_add, hjq, hGq, mul_one]
    have h3 := mul_left_cancel₀ h0 h2
    exact Units.ext (by simpa using h3)
  have hdvd : q ^ 2 - 1 ∣ j * (q - 1) := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one h1
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
  rw [hsq] at hdvd
  obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < q - 1) hdvd
  refine ⟨(g : K) ^ t, ?_⟩
  rw [hφ, ← pow_succ', ← pow_mul, mul_comm t (q + 1), ← ht, hjy]

theorem exists_su2_cube_odd (φ : K →+* K) (q : ℕ) (hφ : ∀ x, φ x = x ^ q)
    (hq : Fintype.card K = q ^ 2) (h2 : (2 : K) ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, (M.map φ)ᵀ * M = 1 ∧ M ^ 3 = 1 ∧ M.det = 1 ∧
      (M 0 1 ≠ 0 ∨ M 0 0 ≠ M 1 1) := by
  have hφφ : ∀ x, φ (φ x) = x := fun x => by
    rw [hφ, hφ, ← pow_mul, ← sq, ← hq, FiniteField.pow_card]
  have hqodd : Odd q := by
    by_contra hqe
    have hev : Even q := Nat.not_odd_iff_even.1 hqe
    have hcev : Even (Fintype.card K) := by
      rw [hq]; exact Nat.even_pow.2 ⟨hev, by norm_num⟩
    have hr : ringChar K = 2 := FiniteField.even_card_iff_char_two.2 (Nat.even_iff.1 hcev)
    exact h2 (by simpa using (ringChar.spec K 2).2 (by rw [hr]))
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Fintype.card K := Fintype.one_lt_card
    rw [hq] at h1
    by_contra hlt
    interval_cases q <;> simp at h1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card, hq]
  obtain ⟨m, hm⟩ := hqodd.add_one
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by simpa using Nat.sq_sub_sq q 1
  have hee : m * (q - 1) + m * (q - 1) = q ^ 2 - 1 := by
    rw [hsq, hm]; ring
  have hge1 : (g : K) ^ (q ^ 2 - 1) = 1 := by
    have := pow_orderOf_eq_one g
    rw [hord] at this
    simpa using congrArg Units.val this
  have hsqe : (g : K) ^ (m * (q - 1)) * (g : K) ^ (m * (q - 1)) = 1 := by
    rw [← pow_add, hee, hge1]
  have hm1 : 1 ≤ m := by omega
  have hn0 : m * (q - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hnlt : m * (q - 1) < orderOf g := by
    rw [hord, ← hee]; omega
  have hne1 : (g : K) ^ (m * (q - 1)) ≠ 1 := fun h =>
    pow_ne_one_of_lt_orderOf hn0 hnlt (Units.ext (by simpa using h))
  have hneg : (g : K) ^ (m * (q - 1)) = -1 :=
    (mul_self_eq_one_iff.1 hsqe).resolve_left hne1
  set c : K := (g : K) ^ m with hc
  have hcne : c ≠ 0 := pow_ne_zero m (Units.ne_zero g)
  have hcneg : φ c = -c := by
    rw [hφ, hc, ← pow_mul]
    have : m * q = m + m * (q - 1) := by
      have : q = 1 + (q - 1) := by omega
      calc m * q = m * (1 + (q - 1)) := by rw [← this]
        _ = m + m * (q - 1) := by ring
    rw [this, pow_add, hneg]; ring
  have hinv : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
  have hφ2 : φ (2 : K)⁻¹ = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  set a : K := -(2 : K)⁻¹ + c with ha
  have hφa : φ a = -(2 : K)⁻¹ - c := by
    rw [ha, map_add, map_neg, hφ2, hcneg]; ring
  have hsum : a + φ a = -1 := by
    rw [hφa, ha]; linear_combination (-1 : K) * hinv
  have hy : φ (1 - a * φ a) = 1 - a * φ a := by
    rw [map_sub, map_one, map_mul, hφφ]; ring
  obtain ⟨b, hb⟩ := exists_norm_eq φ q hφ hq2 g hg hord _ hy
  have hnorm : a * φ a + b * φ b = 1 := by rw [hb]; ring
  have hMt : ((!![a, b; -φ b, φ a] : Matrix (Fin 2) (Fin 2) K).map φ)ᵀ =
      !![φ a, -b; φ b, a] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hφφ]
  have hMM : (!![a, b; -φ b, φ a] : Matrix (Fin 2) (Fin 2) K) * !![a, b; -φ b, φ a] =
      -!![a, b; -φ b, φ a] - 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination a * hsum - hnorm
    · linear_combination b * hsum
    · linear_combination (-φ b) * hsum
    · linear_combination φ a * hsum - hnorm
  refine ⟨!![a, b; -φ b, φ a], ?_, ?_, ?_, Or.inr ?_⟩
  · rw [hMt]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination hnorm
    · ring
    · ring
    · linear_combination hnorm
  · have h1 : (!![a, b; -φ b, φ a] : Matrix (Fin 2) (Fin 2) K) *
        ((!![a, b; -φ b, φ a] : Matrix (Fin 2) (Fin 2) K) * !![a, b; -φ b, φ a]) =
        !![a, b; -φ b, φ a] * (-!![a, b; -φ b, φ a] - 1) := by rw [hMM]
    rw [pow_three, h1, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_one, hMM]
    abel
  · simp [Matrix.det_fin_two]; linear_combination hnorm
  · simp
    intro h
    apply hcne
    have h2c : (2 : K) * c = 0 := by
      rw [hφa, ha] at h; linear_combination h
    exact (mul_eq_zero.1 h2c).resolve_left h2

end Odd

section Final

open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank (psu_three_le_pRank_of_dvd su2_cube_exists)

theorem two_pow_mod_three_cases (f : ℕ) : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
  have h : ¬ 3 ∣ 2 ^ f := fun h => by
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  omega

theorem uniE9_holds : UniE9 := by
  intro n q K _ _ hK hn
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hq0 : q ≠ 0 := by
    have hpos : 0 < q ^ 2 := hcard ▸ Fintype.card_pos
    exact fun h => by subst h; simp at hpos
  by_cases h3 : 3 ∣ q + 1
  · exact le_trans (by norm_num) (psu_three_le_pRank_of_dvd hq0 hK h3 hn)
  obtain ⟨p₀, hp₀⟩ := CharP.exists K
  obtain ⟨f, hpp, hf⟩ := FiniteField.card K p₀
  haveI := Fact.mk hpp
  obtain ⟨e, -, hqe⟩ := (Nat.dvd_prime_pow hpp).1
    (show q ∣ p₀ ^ (f : ℕ) from (hcard.symm.trans hf) ▸ dvd_pow_self q two_ne_zero)
  let φ : K →+* K := iterateFrobenius K p₀ e
  have hφ : ∀ x, φ x = x ^ q := fun x => by
    show x ^ p₀ ^ e = x ^ q
    rw [hqe]
  by_cases h2 : (2 : K) = 0
  · have hp2 : p₀ = 2 := by
      have : p₀ ∣ 2 := (CharP.cast_eq_zero_iff K p₀ 2).1 (by exact_mod_cast h2)
      exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this
    subst hp2
    have h31 : 3 ∣ q - 1 := by
      rcases two_pow_mod_three_cases e with h | h
      · rw [hqe]; omega
      · exact absurd (by rw [hqe]; omega) h3
    have hφφ : ∀ x, φ (φ x) = x := fun x => by
      rw [hφ, hφ, ← pow_mul, ← sq, ← hcard, FiniteField.pow_card]
    have hcube : ∀ x : K, x ^ 3 = 1 → φ x = x := fun x hx => by
      rw [hφ]
      obtain ⟨k, hk⟩ := h31
      have hq1 : 1 ≤ q := by omega
      calc x ^ q = x ^ (q - 1) * x := by rw [← pow_succ, Nat.sub_add_cancel hq1]
        _ = x := by rw [hk, mul_comm, pow_mul, hx, one_pow, mul_one]
    have hcardU : Nat.card Kˣ = (q + 1) * (q - 1) := by
      rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
    have hp : (q + 1).minFac.Prime := Nat.minFac_prime (by omega)
    haveI := Fact.mk hp
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) (q + 1).minFac
      (by rw [hcardU]; exact (Nat.minFac_dvd _).mul_right _)
    have haq : a ^ (q + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [ha]; exact Nat.minFac_dvd _)
    have ha1 : (a : K) ≠ 1 := fun h => by
      have : a = 1 := Units.ext h
      rw [this, orderOf_one] at ha
      exact hp.one_lt.ne ha
    have haφ : φ (a : K) * a = 1 := by
      rw [hφ, ← pow_succ]
      have := congrArg (fun u : Kˣ => (u : K)) haq
      simpa using this
    obtain ⟨M, hM1, hM3, hMdet, hM01⟩ := su2_cube_exists h2 φ hφφ hcube (a : K) haφ ha1
    exact two_le_pRank_of_su2_cube hn φ hφ M hM1 hM3 hMdet (Or.inl hM01)
  · obtain ⟨M, hM1, hM3, hMdet, hMs⟩ := exists_su2_cube_odd φ q hφ hcard h2
    exact two_le_pRank_of_su2_cube hn φ hφ M hM1 hM3 hMdet hMs

end Final

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291
