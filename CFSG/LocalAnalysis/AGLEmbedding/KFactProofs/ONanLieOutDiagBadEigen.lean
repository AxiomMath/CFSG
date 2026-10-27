module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBadBlock
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.AGLEmbedding.LieOut

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups

variable {K : Type} [Field K]

theorem exists_isPrimitiveRoot_five (h : UnitaryFieldData 2 2 K) :
    ∃ ζ : K, IsPrimitiveRoot ζ 5 := by
  have := h.finite
  have hcard : Nat.card Kˣ = 15 := by
    rw [Nat.card_units, h.card]; norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [hcard]; norm_num : 5 ∣ Nat.card Kˣ)
  refine ⟨(g : K), ?_⟩
  have h1 : IsPrimitiveRoot g 5 := hg ▸ IsPrimitiveRoot.orderOf g
  exact h1.map_of_injective (f := Units.coeHom K) Units.val_injective

theorem exists_orthonormal_eigenvectors (h : UnitaryFieldData 2 2 K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hAu : adj h.bar A * A = 1) (hA5 : A ^ 5 = 1) :
    ∃ (v : Fin n → Fin n → K) (μ : Fin n → K), (∀ j, A *ᵥ v j = μ j • v j) ∧
      ∀ i j, (∑ t, h.bar (v i t) * v j t) = if i = j then 1 else 0 := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_five h
  have hiso : ∀ (x y : Fin n → K),
      stdHermForm h n ((Matrix.toLinAlgEquiv' A) x) ((Matrix.toLinAlgEquiv' A) y) =
        stdHermForm h n x y := by
    intro x y
    rw [stdHermForm_eq_gramForm]
    simp only [Matrix.toLinAlgEquiv'_apply]
    rw [gramForm_mulVec]
    have : (A.map h.bar)ᵀ * (1 : Matrix (Fin n) (Fin n) K) * A = 1 := by
      rw [Matrix.mul_one]; exact hAu
    rw [this]
  have hpow : (Matrix.toLinAlgEquiv' A) ^ 5 = 1 := by
    rw [← map_pow, hA5]
    exact map_one _
  obtain ⟨b, μ, hμ, hb⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis h hζ
      (by norm_num : 5 ∣ 2 ^ 2 + 1) (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n)
      (ι := Unit) (fun _ => Matrix.toLinAlgEquiv' A) (fun _ _ => Commute.refl _)
      (fun _ => hpow) (fun _ => hiso)
  have hr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  refine ⟨fun i => b (Fin.cast hr.symm i), fun j => μ () (Fin.cast hr.symm j), fun j => ?_,
    fun i j => ?_⟩
  · have := hμ () (Fin.cast hr.symm j)
    simpa [Matrix.toLinAlgEquiv'_apply] using this
  · have := hb (Fin.cast hr.symm i) (Fin.cast hr.symm j)
    simp only [stdHermForm_apply] at this
    rw [this]
    simp [Fin.cast_inj]

theorem pow_mulVec_of_eigen {n : ℕ} {A : Matrix (Fin n) (Fin n) K} {w : Fin n → K} {μ : K}
    (hw : A *ᵥ w = μ • w) (k : ℕ) : (A ^ k) *ᵥ w = μ ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hw, smul_smul, pow_succ',
      mul_comm]

theorem det_eq_prod_of_eigen {n : ℕ} (h : UnitaryFieldData 2 2 K) (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → Fin n → K) (μ : Fin n → K) (hv : ∀ j, A *ᵥ v j = μ j • v j)
    (hon : ∀ i j, (∑ t, h.bar (v i t) * v j t) = if i = j then 1 else 0) :
    A.det = ∏ j, μ j := by
  classical
  set P : Matrix (Fin n) (Fin n) K := Matrix.of fun t j => v j t with hP
  have hAP : A * P = P * Matrix.diagonal μ := by
    ext t j
    have := congrFun (hv j) t
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp [Matrix.mul_apply, hP, Matrix.diagonal_apply, this, mul_comm]
  have hPP : adj h.bar P * P = 1 := by
    ext i j
    simp [adj, Matrix.mul_apply, hP, hon i j, Matrix.one_apply]
  have hdetP : P.det ≠ 0 := by
    have := congrArg det hPP
    rw [det_mul, det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have := congrArg det hAP
  rw [det_mul, det_mul, det_diagonal] at this
  exact mul_right_cancel₀ hdetP (by rw [this, mul_comm])

theorem prod_pow_eq_one_of_fibers {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ 5) (hn : 10 ≤ n)
    (e : Fin n → Fin 5) (hle : ∀ i, (Finset.univ.filter fun j => e j = i).card ≤ 2) :
    ∏ j, ζ ^ (e j : ℕ) = 1 := by
  classical
  have hsum : ∑ i : Fin 5, (Finset.univ.filter fun j => e j = i).card = n := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := e) (fun j _ => Finset.mem_univ _)]
    simp
  have hc : ∀ i, (Finset.univ.filter fun j => e j = i).card = 2 := by
    intro i
    rw [Fin.sum_univ_five] at hsum
    have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    have h3 := hle 3
    have h4 := hle 4
    fin_cases i <;> simp <;> omega
  calc ∏ j, ζ ^ (e j : ℕ)
      = ∏ i : Fin 5, ∏ j ∈ Finset.univ.filter (fun j => e j = i), ζ ^ (e j : ℕ) :=
        (Finset.prod_fiberwise Finset.univ e _).symm
    _ = ∏ i : Fin 5, ζ ^ ((i : ℕ) * 2) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]),
          Finset.prod_const, hc i, ← pow_mul]
    _ = ζ ^ 20 := by
        rw [Fin.prod_univ_five, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        rfl
    _ = 1 := by rw [show 20 = 5 * 4 from rfl, pow_mul, hζ.pow_eq_one, one_pow]

theorem exists_frame {n : ℕ} (h : UnitaryFieldData 2 2 K) (hn : 10 ≤ n)
    (A : Matrix (Fin n) (Fin n) K) (hAu : adj h.bar A * A = 1) (hA5 : A ^ 5 = 1)
    (hdet : A.det ≠ 1) :
    ∃ (B : Matrix (Fin n) (Fin 3) K) (ζ : K), ζ ^ 5 = 1 ∧ adj h.bar B * B = 1 ∧
      A * B = ζ • B := by
  classical
  obtain ⟨v, μ, hv, hon⟩ := exists_orthonormal_eigenvectors h A hAu hA5
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_five h
  have hv0 : ∀ j, v j ≠ 0 := by
    intro j hj
    have := hon j j
    simp [hj] at this
  have hμ5 : ∀ j, μ j ^ 5 = 1 := by
    intro j
    have h1 := pow_mulVec_of_eigen (hv j) 5
    rw [hA5, Matrix.one_mulVec] at h1
    have h2 : (1 - μ j ^ 5) • v j = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact (sub_eq_zero.1 h3).symm
    · exact absurd h3 (hv0 j)
  have hex : ∀ j, ∃ i : Fin 5, ζ₀ ^ (i : ℕ) = μ j := by
    intro j
    obtain ⟨i, hi, hi'⟩ := hζ₀.eq_pow_of_pow_eq_one (hμ5 j)
    exact ⟨⟨i, hi⟩, hi'⟩
  choose e he using hex
  by_cases hbig : ∃ i : Fin 5, 2 < (Finset.univ.filter fun j => e j = i).card
  · obtain ⟨i, hi⟩ := hbig
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hi
    have hfib : ∀ j, j ∈ (Finset.univ.filter fun j => e j = i) → μ j = ζ₀ ^ (i : ℕ) := by
      intro j hj
      rw [← he j, (Finset.mem_filter.1 hj).2]
    let idx : Fin 3 → Fin n := ![a, b, c]
    have hidx : Function.Injective idx := by
      intro r s hrs
      fin_cases r <;> fin_cases s <;> simp_all [idx]
    have hidxmem : ∀ r, idx r ∈ (Finset.univ.filter fun j => e j = i) := by
      intro r
      fin_cases r <;> simp_all [idx]
    refine ⟨Matrix.of fun t r => v (idx r) t, ζ₀ ^ (i : ℕ), ?_, ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow]
    · ext r s
      simp only [adj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
      rw [hon (idx r) (idx s)]
      simp [Matrix.one_apply, hidx.eq_iff]
    · ext t r
      have := congrFun (hv (idx r)) t
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      rw [this, hfib _ (hidxmem r)]
  · exfalso
    push Not at hbig
    apply hdet
    rw [det_eq_prod_of_eigen h A v μ hv hon]
    calc ∏ j, μ j = ∏ j, ζ₀ ^ ((e j : Fin 5) : ℕ) :=
          Finset.prod_congr rfl fun j _ => (he j).symm
      _ = 1 := prod_pow_eq_one_of_fibers hζ₀ hn e hbig

theorem adj_mul_eq {n k : ℕ} (h : UnitaryFieldData 2 2 K) (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin k) K) {ζ : K} (hζ5 : ζ ^ 5 = 1) (hAu : adj h.bar A * A = 1)
    (hAB : A * B = ζ • B) : adj h.bar B * A = ζ • adj h.bar B := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    norm_num at hζ5
  have step1 : adj h.bar A * B = ζ⁻¹ • B := by
    have hB : B = ζ⁻¹ • (A * B) := by
      rw [hAB, smul_smul, inv_mul_cancel₀ hζ0, one_smul]
    calc adj h.bar A * B = adj h.bar A * (ζ⁻¹ • (A * B)) := by rw [← hB]
      _ = ζ⁻¹ • (adj h.bar A * A * B) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = ζ⁻¹ • B := by rw [hAu, Matrix.one_mul]
  have step2 := congrArg (adj h.bar) step1
  rw [adj_mul, adj_adj h.bar h.bar_bar, adj_smul] at step2
  have step3 : h.bar ζ⁻¹ = ζ := by
    rw [UnitaryFieldData.bar_apply, inv_pow]
    have : ζ ^ 2 ^ 2 = ζ⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      calc ζ ^ 2 ^ 2 * ζ = ζ ^ 5 := by ring
        _ = 1 := hζ5
    rw [this, inv_inv]
  rw [step3] at step2
  exact step2

theorem thirteen_dvd_card_su_three (h : UnitaryFieldData 2 2 K) :
    13 ∣ Nat.card (gramSU h (1 : Matrix (Fin 3) (Fin 3) K)) := by
  have := h.finite
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 3) (Fin 3) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [← card_gramSU] at hU
  have h2 : Finset.Icc 2 3 = {2, 3} := by decide
  rw [h2, Finset.prod_pair (by norm_num)] at hU
  norm_num at hU
  have : (13 : ℤ) ∣ (Nat.card (gramSU h (1 : Matrix (Fin 3) (Fin 3) K)) : ℤ) := by
    rw [hU]; norm_num
  exact_mod_cast this

theorem exists_matrix_order_thirteen (h : UnitaryFieldData 2 2 K) :
    ∃ M : Matrix (Fin 3) (Fin 3) K, adj h.bar M * M = 1 ∧ M ^ 13 = 1 ∧ M ≠ 1 := by
  classical
  have := h.finite
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 13 (thirteen_dvd_card_su_three h)
  have hg13 : g ^ 13 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hgu : adj h.bar ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := g.2.1
    rwa [Matrix.mul_one] at this
  refine ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hgu, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hg13]
    rfl
  · intro h1
    have : g = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact h1
    rw [this, orderOf_one] at hg
    omega

theorem exists_order_thirteen {n : ℕ} (h : UnitaryFieldData 2 2 K) (hn : 10 ≤ n)
    (A : Matrix (Fin n) (Fin n) K) (hAu : adj h.bar A * A = 1) (hA5 : A ^ 5 = 1)
    (hdet : A.det ≠ 1) :
    ∃ u : Matrix (Fin n) (Fin n) K, adj h.bar u * u = 1 ∧ A * u = u * A ∧ u ^ 13 = 1 ∧
      u ≠ 1 := by
  obtain ⟨B, ζ, hζ5, hB, hAB⟩ := exists_frame h hn A hAu hA5 hdet
  obtain ⟨M, hMu, hM13, hM1⟩ := exists_matrix_order_thirteen h
  have hBA := adj_mul_eq h A B hζ5 hAu hAB
  refine ⟨frame h.bar B M, adj_frame_mul_frame h.bar_bar hB hMu, frame_commute hAB hBA M,
    ?_, fun hu => hM1 (eq_one_of_frame_eq_one hB hu)⟩
  rw [frame_pow hB, hM13, frame_one]

end CFSG.AGLEmbedding.LieOut
