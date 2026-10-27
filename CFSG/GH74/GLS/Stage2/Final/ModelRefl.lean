module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Orders.Basic
public import CFSG.GH74.GLS.Stage2.Final.ModelBlock

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

@[expose] def dRefl (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

variable {F : Type} [Field F]

theorem coe_dRefl : ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, -1] := rfl

theorem dRefl_mul_self : dRefl F * dRefl F = 1 := by
  apply Units.ext
  simp [coe_dRefl, Matrix.one_fin_two]

theorem det_dRefl : ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  simp [coe_dRefl, Matrix.det_fin_two]

theorem ch_sq {a : GL (Fin 2) F} {c : Fˣ} (h : a * a = sc2 c) :
    (∃ l : Fˣ, a = sc2 l ∧ l * l = c) ∨
      ((a : Matrix (Fin 2) (Fin 2) F).trace = 0 ∧ (a : Matrix (Fin 2) (Fin 2) F).det = -(c : F)) := by
  have hm : (a : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) =
      (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h
    simpa [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] using this
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases htr : (a : Matrix (Fin 2) (Fin 2) F).trace = 0
  · right
    refine ⟨htr, ?_⟩
    rw [Matrix.trace_fin_two] at htr
    rw [Matrix.det_fin_two]
    have hs : (a : Matrix (Fin 2) (Fin 2) F) 1 1 = -(a : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      linear_combination htr
    rw [hs]
    linear_combination -e00
  · left
    rw [Matrix.trace_fin_two] at htr
    have hq : (a : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      have : (a : Matrix (Fin 2) (Fin 2) F) 0 1 *
          ((a : Matrix (Fin 2) (Fin 2) F) 0 0 + (a : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right htr
    have hr : (a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (a : Matrix (Fin 2) (Fin 2) F) 1 0 *
          ((a : Matrix (Fin 2) (Fin 2) F) 0 0 + (a : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right htr
    have hps : (a : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      have : ((a : Matrix (Fin 2) (Fin 2) F) 0 0 - (a : Matrix (Fin 2) (Fin 2) F) 1 1) *
          ((a : Matrix (Fin 2) (Fin 2) F) 0 0 + (a : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
        rw [hq, hr] at e00 e11
        linear_combination e00 - e11
      have := (mul_eq_zero.1 this).resolve_right htr
      linear_combination this
    have hp0 : (a : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0
      rw [hq, hr, h0] at e00
      have : (c : F) = 0 := by linear_combination -e00
      exact c.ne_zero this
    refine ⟨Units.mk0 _ hp0, ?_, ?_⟩
    · apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hq, hr, hps]
    · apply Units.ext
      rw [hq, hr] at e00
      simp only [Units.val_mul, Units.val_mk0]
      linear_combination e00


theorem exists_pow_succ_eq {F : Type} [Field F] [Finite F] {q : ℕ} (hq : 2 ≤ q)
    (hF : Nat.card F = q ^ 2) {t : F} (ht0 : t ≠ 0) (htq : t ^ q = t) :
    ∃ l : F, l ^ (q + 1) = t := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Nat.card Fˣ = q ^ 2 - 1 := by rw [Nat.card_units, hF]
  have hord : orderOf g = q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  set tu : Fˣ := Units.mk0 t ht0 with htu
  obtain ⟨n, hn⟩ : ∃ n : ℕ, g ^ n = tu := by
    have := mem_powers_iff_mem_zpowers.2 (hg tu)
    exact this
  have h1 : tu ^ q = tu := Units.ext (by simpa [htu] using htq)
  have h2 : g ^ (n * (q - 1)) = 1 := by
    have h3 : g ^ (n * q) = g ^ n := by rw [pow_mul, hn, h1]
    have h4 : g ^ (n * q) = g ^ (n * (q - 1)) * g ^ n := by
      rw [← pow_add]
      congr 1
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp [Nat.mul_succ]
    rw [h4] at h3
    have : g ^ (n * (q - 1)) * g ^ n = 1 * g ^ n := by rw [h3, one_mul]
    exact mul_right_cancel this
  have h5 : (q ^ 2 - 1) ∣ n * (q - 1) := by
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one h2
  have h6 : (q - 1) * (q + 1) ∣ (q - 1) * n := by
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [Nat.pow_two]
      have : (q' + 1) * (q' + 1) - 1 = q' * (q' + 2) := by
        cases q' with
        | zero => omega
        | succ r => ring_nf; omega
      rw [this]
    rw [this, mul_comm n] at h5
    exact h5
  have h7 : (q + 1) ∣ n := Nat.dvd_of_mul_dvd_mul_left (by omega) h6
  obtain ⟨m, hm⟩ := h7
  refine ⟨((g ^ m : Fˣ) : F), ?_⟩
  have : (g ^ m) ^ (q + 1) = tu := by rw [← pow_mul, mul_comm, ← hm, hn]
  have := congrArg (fun u : Fˣ => (u : F)) this
  simpa [htu] using this


theorem refl_trace_det {a : GL (Fin 2) F} (ha : a * a = 1) (h1 : a ≠ 1)
    (hm1 : a ≠ -1) :
    (a : Matrix (Fin 2) (Fin 2) F).trace = 0 ∧ (a : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  have hc : a * a = sc2 1 := by rw [ha]; simp [sc2]
  rcases ch_sq hc with ⟨l, hl, hll⟩ | ⟨ht, hd⟩
  · exfalso
    rcases units_sq_eq_one hll with rfl | rfl
    · exact h1 (by rw [hl]; simp [sc2])
    · exact hm1 (by rw [hl]; simp [sc2, CFSG.GH74.L5U5.scalar_neg_one_eq])
  · exact ⟨ht, by simpa using hd⟩

theorem exists_eigen_matrix (h2 : (2 : F) ≠ 0) {a : GL (Fin 2) F} (ha : a * a = 1) (h1 : a ≠ 1)
    (hm1 : a ≠ -1) :
    ∃ X : Matrix (Fin 2) (Fin 2) F, X.det ≠ 0 ∧
      (a : Matrix (Fin 2) (Fin 2) F) * X = X * !![1, 0; 0, -1] := by
  obtain ⟨htr, hdet⟩ := refl_trace_det ha h1 hm1
  set A : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hA
  have hAA : A * A = 1 := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) ha
    simpa using this
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have hs : A 1 1 = -A 0 0 := by linear_combination htr
  have hpq : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    rw [hs] at hdet; linear_combination -hdet
  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → F, u 0 * (A *ᵥ u) 1 - u 1 * (A *ᵥ u) 0 ≠ 0 := by
    by_cases hr : A 1 0 = 0
    · by_cases hq : A 0 1 = 0
      · refine ⟨![1, 1], ?_⟩
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        simp [hr, hq, hs]
        intro h
        have h' : (2 : F) * A 0 0 = 0 := by linear_combination -h
        have hp0 : A 0 0 = 0 := (mul_eq_zero.1 h').resolve_left h2
        rw [hp0, hq, hr] at hpq
        simp at hpq
      · refine ⟨![0, 1], ?_⟩
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        exact hq
    · refine ⟨![1, 0], ?_⟩
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact hr
  set w := A *ᵥ u with hw
  have hAw : A *ᵥ w = u := by rw [hw, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hw0 : w 0 = A 0 0 * u 0 + A 0 1 * u 1 := by
    simp [hw]
  have hw1 : w 1 = A 1 0 * u 0 + A 1 1 * u 1 := by
    simp [hw]
  have e0 : A 0 0 * w 0 + A 0 1 * w 1 = u 0 := by
    have := congrFun hAw 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e1 : A 1 0 * w 0 + A 1 1 * w 1 = u 1 := by
    have := congrFun hAw 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  refine ⟨!![u 0 + w 0, u 0 - w 0; u 1 + w 1, u 1 - w 1], ?_, ?_⟩
  · intro h
    apply hu
    have h' : (2 : F) * (u 0 * w 1 - u 1 * w 0) = 0 := by
      rw [Matrix.det_fin_two] at h
      simp at h
      linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left h2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination e0 - hw0
    · linear_combination -hw0 - e0
    · linear_combination e1 - hw1
    · linear_combination -hw1 - e1


theorem refl_conj_lin (h2 : (2 : F) ≠ 0) {a : GL (Fin 2) F} (ha : a * a = 1) (h1 : a ≠ 1)
    (hm1 : a ≠ -1) :
    ∃ x : GL (Fin 2) F, (x : Matrix (Fin 2) (Fin 2) F).det = 1 ∧ x * a * x⁻¹ = dRefl F := by
  obtain ⟨X, hX, hAX⟩ := exists_eigen_matrix h2 ha h1 hm1
  set s : F := (X.det)⁻¹ with hs
  set X' : Matrix (Fin 2) (Fin 2) F := X * !![1, 0; 0, s] with hX'
  have hdet' : X'.det = 1 := by
    have hd : (!![1, 0; 0, s] : Matrix (Fin 2) (Fin 2) F).det = s := by
      simp [Matrix.det_fin_two]
    rw [hX', Matrix.det_mul, hd, hs]
    exact mul_inv_cancel₀ hX
  have hcomm : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, s] =
      !![1, 0; 0, s] * !![1, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hAX' : (a : Matrix (Fin 2) (Fin 2) F) * X' = X' * !![1, 0; 0, -1] := by
    rw [hX', ← Matrix.mul_assoc, hAX, Matrix.mul_assoc, Matrix.mul_assoc, hcomm]
  let G : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero X' (by rw [hdet']; exact one_ne_zero)
  have hG : (G : Matrix (Fin 2) (Fin 2) F) = X' := rfl
  have hGa : a * G = G * dRefl F := by
    apply Units.ext
    simp only [Units.val_mul, hG, coe_dRefl]
    exact hAX'
  refine ⟨G⁻¹, ?_, ?_⟩
  · have hd : Matrix.GeneralLinearGroup.det G = 1 := Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hG, hdet']; rfl)
    have := Matrix.GeneralLinearGroup.val_det_apply (G⁻¹)
    rw [← this, map_inv, hd]
    simp
  · rw [inv_inv, mul_assoc, hGa, ← mul_assoc, inv_mul_cancel, one_mul]



section Uni

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

theorem Dm_eq_diag {F : Type} [Field F] :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(1 : F), -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem diag_comm_Dm {F : Type} [Field F] (d : Fin 2 → F) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal d =
      Matrix.diagonal d * !![1, 0; 0, -1] := by
  rw [Dm_eq_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem scale_eigen {F : Type} [Field F] {A X : Matrix (Fin 2) (Fin 2) F} (d : Fin 2 → F)
    (h : A * X = X * !![1, 0; 0, -1]) :
    A * (X * Matrix.diagonal d) = (X * Matrix.diagonal d) * !![1, 0; 0, -1] := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.mul_assoc, diag_comm_Dm]

theorem conjTr_diagonal' {F : Type} [Field F] (σ : F ≃+* F) (v : Fin 2 → F) :
    conjTr σ (Matrix.diagonal v) = Matrix.diagonal fun i => σ (v i) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [conjTr]
  · simp [conjTr, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem gram_scale {F : Type} [Field F] (σ : F ≃+* F) (X : Matrix (Fin 2) (Fin 2) F) (d : Fin 2 → F) :
    conjTr σ (X * Matrix.diagonal d) * (X * Matrix.diagonal d) =
      Matrix.diagonal (fun i => σ (d i)) * (conjTr σ X * X) * Matrix.diagonal d := by
  rw [conjTr_mul, conjTr_diagonal']
  simp only [Matrix.mul_assoc]

theorem refl_conj_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) {a : GL (Fin 2) F}
    (haU : a ∈ uniGL (unitaryInvolution F p f) 2) (ha : a * a = 1) (h1 : a ≠ 1) (hm1 : a ≠ -1) :
    ∃ x : GL (Fin 2) F, x ∈ uniGL (unitaryInvolution F p f) 2 ∧
      (x : Matrix (Fin 2) (Fin 2) F).det = 1 ∧ x * a * x⁻¹ = dRefl F := by
  set σ := unitaryInvolution F p f with hσdef
  have hσ : ∀ x, σ x = x ^ (p ^ f) := unitaryInvolution_apply F p f
  have hσσ : ∀ x, σ (σ x) = x := unitaryInvolution_involutive hF
  have h2 : (2 : F) ≠ 0 := by
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    exact CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow (Fact.out : p.Prime) hp2 hF'
  have hq2 : 2 ≤ p ^ f := by
    have h1' : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1'
    by_contra hlt
    have h3 : p ^ f ≤ 1 := by omega
    have h4 : (p ^ f) ^ 2 ≤ 1 := by
      calc (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h3 2
        _ = 1 := by norm_num
    omega
  obtain ⟨X, hXdet, hAX⟩ := exists_eigen_matrix h2 ha h1 hm1
  set A : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hA
  have hU : conjTr σ A * A = 1 := haU
  set Dm : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, -1] with hDm
  have hDmc : conjTr σ Dm = Dm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [conjTr, Dm]
  set G : Matrix (Fin 2) (Fin 2) F := conjTr σ X * X with hG
  have hGD : G = Dm * G * Dm := by
    calc G = conjTr σ X * (conjTr σ A * A) * X := by rw [hU, mul_one]
      _ = conjTr σ (A * X) * (A * X) := by rw [conjTr_mul]; simp only [Matrix.mul_assoc]
      _ = conjTr σ (X * Dm) * (X * Dm) := by rw [hAX]
      _ = Dm * G * Dm := by rw [conjTr_mul, hDmc]; simp only [hG, Matrix.mul_assoc]
  have hDd : Dm = Matrix.diagonal ![(1 : F), -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Dm, Matrix.diagonal]
  have hG01 : G 0 1 = 0 := by
    have := congrFun (congrFun hGD 0) 1
    rw [hDd] at this
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    simp at this
    have h' : (2 : F) * G 0 1 = 0 := by linear_combination this
    exact (mul_eq_zero.1 h').resolve_left h2
  have hG10 : G 1 0 = 0 := by
    have := congrFun (congrFun hGD 1) 0
    rw [hDd] at this
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    simp at this
    have h' : (2 : F) * G 1 0 = 0 := by linear_combination this
    exact (mul_eq_zero.1 h').resolve_left h2
  set gp : F := G 0 0 with hgp
  set gm : F := G 1 1 with hgm
  have hGdiag : G = Matrix.diagonal ![gp, gm] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hG01, hG10, hgp, hgm]
  have hdetX : σ X.det ≠ 0 := by
    intro h; exact hXdet (by simpa using h)
  have hdetG : G.det = σ X.det * X.det := by
    rw [hG, Matrix.det_mul]
    congr 1
    simp only [conjTr, Matrix.det_transpose]
    exact (RingHom.map_det (σ : F →+* F) X).symm
  have hgg : gp * gm = σ X.det * X.det := by
    rw [← hdetG, hGdiag, Matrix.det_diagonal]
    simp [Fin.prod_univ_two]
  have hggne : gp * gm ≠ 0 := by rw [hgg]; exact mul_ne_zero hdetX hXdet
  have hgp0 : gp ≠ 0 := left_ne_zero_of_mul hggne
  have hgm0 : gm ≠ 0 := right_ne_zero_of_mul hggne
  have hσgp : σ gp = gp := by
    have : gp = σ (X 0 0) * X 0 0 + σ (X 1 0) * X 1 0 := by
      simp [hgp, hG, Matrix.mul_apply, Fin.sum_univ_two, conjTr]
    rw [this, map_add, map_mul, map_mul, hσσ, hσσ]
    ring
  have hσgm : σ gm = gm := by
    have : gm = σ (X 0 1) * X 0 1 + σ (X 1 1) * X 1 1 := by
      simp [hgm, hG, Matrix.mul_apply, Fin.sum_univ_two, conjTr]
    rw [this, map_add, map_mul, map_mul, hσσ, hσσ]
    ring
  have hσinv : ∀ g : F, σ g = g → (g⁻¹) ^ (p ^ f) = g⁻¹ := fun g hg => by
    rw [← hσ, map_inv₀, hg]
  obtain ⟨lp, hlp⟩ := exists_pow_succ_eq hq2 hF (inv_ne_zero hgp0) (hσinv gp hσgp)
  obtain ⟨lm, hlm⟩ := exists_pow_succ_eq hq2 hF (inv_ne_zero hgm0) (hσinv gm hσgm)
  have hσlp : σ lp * lp = gp⁻¹ := by rw [hσ, ← pow_succ, hlp]
  have hσlm : σ lm * lm = gm⁻¹ := by rw [hσ, ← pow_succ, hlm]
  set X₁ : Matrix (Fin 2) (Fin 2) F := X * Matrix.diagonal ![lp, lm] with hX₁
  have hAX₁ : A * X₁ = X₁ * Dm := scale_eigen _ hAX
  have hU₁ : conjTr σ X₁ * X₁ = 1 := by
    rw [hX₁, gram_scale, ← hG, hGdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simp
      rw [mul_assoc, mul_comm gp, ← mul_assoc, hσlp, inv_mul_cancel₀ hgp0]
    · simp
      rw [mul_assoc, mul_comm gm, ← mul_assoc, hσlm, inv_mul_cancel₀ hgm0]
  have hδ : σ X₁.det * X₁.det = 1 := by
    have := congrArg Matrix.det hU₁
    rw [Matrix.det_mul, Matrix.det_one] at this
    have h' : (conjTr σ X₁).det = σ X₁.det := by
      simp only [conjTr, Matrix.det_transpose]
      exact (RingHom.map_det (σ : F →+* F) X₁).symm
    rwa [h'] at this
  set δ := X₁.det with hδdef
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hδ
    exact zero_ne_one hδ
  set X₂ : Matrix (Fin 2) (Fin 2) F := X₁ * Matrix.diagonal ![(1 : F), δ⁻¹] with hX₂
  have hAX₂ : A * X₂ = X₂ * Dm := scale_eigen _ hAX₁
  have hU₂ : conjTr σ X₂ * X₂ = 1 := by
    rw [hX₂, gram_scale, hU₁, Matrix.mul_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i
    · simp
    · simp
      rw [← mul_inv, hδ, inv_one]
  have hdet₂ : X₂.det = 1 := by
    rw [hX₂, Matrix.det_mul, Matrix.det_diagonal]
    simp [Fin.prod_univ_two]
    exact mul_inv_cancel₀ hδ0
  let G₂ : GL (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero X₂ (by rw [hdet₂]; exact one_ne_zero)
  have hG₂ : (G₂ : Matrix (Fin 2) (Fin 2) F) = X₂ := rfl
  have hGa : a * G₂ = G₂ * dRefl F := by
    apply Units.ext
    simp only [Units.val_mul, hG₂, coe_dRefl]
    exact hAX₂
  have hinv : ((G₂⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = conjTr σ X₂ := by
    rw [Matrix.GeneralLinearGroup.coe_inv, hG₂]
    exact Matrix.inv_eq_left_inv hU₂
  have hcc : ∀ M : Matrix (Fin 2) (Fin 2) F, conjTr σ (conjTr σ M) = M := by
    intro M; ext i j; simp [conjTr, hσσ]
  refine ⟨G₂⁻¹, ?_, ?_, ?_⟩
  · show conjTr σ ((G₂⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((G₂⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [hinv, hcc]
    have hu : IsUnit X₂.det := by rw [hdet₂]; exact isUnit_one
    have h3 : conjTr σ X₂ = X₂⁻¹ := (Matrix.inv_eq_left_inv hU₂).symm
    rw [h3]
    exact Matrix.mul_nonsing_inv X₂ hu
  · have hd : Matrix.GeneralLinearGroup.det G₂ = 1 :=
      Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hG₂, hdet₂]; rfl)
    have := Matrix.GeneralLinearGroup.val_det_apply (G₂⁻¹)
    rw [← this, map_inv, hd]
    simp
  · rw [inv_inv, mul_assoc, hGa, ← mul_assoc, inv_mul_cancel, one_mul]

end Uni

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg in
theorem dRefl_mem_uni {σ : F ≃+* F} : dRefl F ∈ uniGL σ 2 := by
  show conjTr σ ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
    ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
  have h := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) (dRefl_mul_self (F := F))
  simp only [Units.val_mul, Units.val_one] at h
  have hc : conjTr σ ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((dRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [conjTr, coe_dRefl]
  rw [hc]
  exact h

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
