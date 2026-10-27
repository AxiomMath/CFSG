module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LInner1

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type} [Field K] {N : Matrix (Fin n) (Fin n) K}

theorem idem_mul {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) (α β γ δ : K) :
    (α • (1 - P) + β • P) * (γ • (1 - P) + δ • P) = (α * γ) • (1 - P) + (β * δ) • P := by
  have h1 : (1 - P) * (1 - P) = 1 - P := by
    rw [show (1 - P) * (1 - P) = 1 - P - P + P * P by noncomm_ring, hP]
    abel
  have h2 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  have h3 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, hP, smul_zero, add_zero,
    zero_add]

theorem idem_pow {P : Matrix (Fin n) (Fin n) K} (hP : P * P = P) (α β : K) (m : ℕ) :
    (α • (1 - P) + β • P) ^ m = α ^ m • (1 - P) + β ^ m • P := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, one_smul, one_smul, sub_add_cancel]
  | succ m ih => rw [pow_succ, ih, idem_mul hP, ← pow_succ, ← pow_succ]

theorem exists_indep_ker (hn : 3 ≤ n) (φ : Fin n → K) {y : Fin n → K} (hy : φ ⬝ᵥ y = 0)
    (hy0 : y ≠ 0) : ∃ x : Fin n → K, φ ⬝ᵥ x = 0 ∧ LinearIndependent K ![y, x] := by
  set W := LinearMap.ker (Matrix.of ![φ]).mulVecLin with hW
  have hmem : ∀ x : Fin n → K, x ∈ W ↔ φ ⬝ᵥ x = 0 := by
    intro x
    rw [hW, LinearMap.mem_ker, mulVecLin_apply]
    constructor
    · intro h
      simpa [mulVec, Matrix.of_apply] using congrFun h 0
    · intro h0
      ext i
      fin_cases i
      simpa [mulVec, Matrix.of_apply]
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.of ![φ]).mulVecLin
  have hle : Module.finrank K (LinearMap.range (Matrix.of ![φ]).mulVecLin) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (Matrix.of ![φ]).mulVecLin)
    simpa using this
  rw [Module.finrank_fin_fun, ← hW] at hrk
  have hW2 : 1 < Module.finrank K W := by omega
  have hyW : y ∈ W := (hmem y).mpr hy
  obtain ⟨x', hxx'⟩ := exists_linearIndependent_pair_of_one_lt_finrank hW2
    (x := ⟨y, hyW⟩) (fun h => hy0 (congrArg Subtype.val h))
  have hp := LinearIndependent.pair_iff.mp hxx'
  refine ⟨x', (hmem x').mp x'.2, LinearIndependent.pair_iff.mpr fun s t hst => hp s t ?_⟩
  exact Subtype.ext (by simpa using hst)

theorem exists_dual_ne_zero (hn : 3 ≤ n) (x y : Fin n → K) :
    ∃ ρ : Fin n → K, ρ ≠ 0 ∧ ρ ⬝ᵥ x = 0 ∧ ρ ⬝ᵥ y = 0 := by
  set W := LinearMap.ker (Matrix.of ![x, y]).mulVecLin with hW
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.of ![x, y]).mulVecLin
  have hle : Module.finrank K (LinearMap.range (Matrix.of ![x, y]).mulVecLin) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range (Matrix.of ![x, y]).mulVecLin)
    simpa using this
  rw [Module.finrank_fin_fun, ← hW] at hrk
  obtain ⟨ρ, hρ⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < Module.finrank K W)
  have h := LinearMap.mem_ker.mp ρ.2
  rw [mulVecLin_apply] at h
  refine ⟨ρ, fun h0 => hρ (Subtype.ext h0), ?_, ?_⟩
  · rw [dotProduct_comm]
    simpa [mulVec, Matrix.of_apply] using congrFun h 0
  · rw [dotProduct_comm]
    simpa [mulVec, Matrix.of_apply] using congrFun h 1

theorem ringChar_eq_two (h2 : (2 : K) = 0) : ringChar K = 2 := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  exact ringChar.eq K 2

theorem hasWit_of_rank_one_three [Finite K] (h2 : (2 : K) = 0) (hn : n = 3)
    (hK : 8 ≤ Nat.card K) {A : GL (Fin n) K} {μ : K}
    (hNA : N = (A : Matrix (Fin n) (Fin n) K) + μ • 1) {f₀ φ₀ : Fin n → K}
    (hy0 : N *ᵥ f₀ ≠ 0) (hNy : N = vecMulVec (N *ᵥ f₀) φ₀) (hφy : φ₀ ⬝ᵥ (N *ᵥ f₀) = 0) :
    HasWit (conjAut n K A) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨y, hy⟩ : ∃ y, y = N *ᵥ f₀ := ⟨_, rfl⟩
  rw [← hy] at hy0 hφy
  have hNy' : N = vecMulVec y φ₀ := by rw [hy]; exact hNy
  obtain ⟨x, hφx, hind⟩ := exists_indep_ker (by omega) φ₀ hφy hy0
  have hp := LinearIndependent.pair_iff.mp hind
  have hxs : x ∉ Submodule.span K {y} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := hp c (-1) (by rw [hc, neg_smul, one_smul, add_neg_cancel])
    exact one_ne_zero (neg_eq_zero.mp this.2)
  obtain ⟨χ, hχx, hχW⟩ := exists_dotProduct_of_notMem hxs
  have hχy : χ ⬝ᵥ y = 0 := hχW _ (Submodule.mem_span_singleton_self y)
  obtain ⟨ρ, hρ0, hρx, hρy⟩ := exists_dual_ne_zero (by omega) x y
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Fintype.card Kˣ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hcardU : Fintype.card Kˣ = Fintype.card K - 1 := Fintype.card_units K
  rw [Nat.card_eq_fintype_card] at hK
  obtain ⟨l, hl⟩ : ∃ l : K, l = g := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := by rw [hl]; exact g.ne_zero
  have hl3 : l ^ 3 ≠ 1 := by
    intro h3
    have : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one
      (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, ← hl]; exact h3))
    rw [hord, hcardU] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hev := (FiniteField.even_card_iff_char_two (F := K)).mp (ringChar_eq_two h2)
  have hm : Odd (Fintype.card K - 1) := Nat.odd_iff.mpr (by omega)
  set P := vecMulVec x χ with hP
  have hPP : P * P = P := by rw [hP, vecMulVec_mul_vecMulVec, hχx, one_smul]
  set T : Matrix (Fin n) (Fin n) K := l • (1 - P) + (l⁻¹ ^ 2) • P with hT
  have hdet : T.det = 1 := by
    have hT' : T = l • (1 + vecMulVec x ((l⁻¹ * (l⁻¹ ^ 2 - l)) • χ)) := by
      rw [hT, hP]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply,
        smul_eq_mul, Pi.smul_apply]
      field_simp
      ring
    subst hn
    rw [hT', det_smul, Fintype.card_fin, vecMulVec_eq (ι := Unit),
      det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, hχx, smul_eq_mul, mul_one]
    field_simp
    ring
  set τ : SpecialLinearGroup (Fin n) K := ⟨T, hdet⟩ with hτ
  have hτT : (τ : Matrix (Fin n) (Fin n) K) = T := rfl
  have hτm : τ ^ (Fintype.card K - 1) = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hτT, hT, idem_pow hPP,
      FiniteField.pow_card_sub_one_eq_one l hl0,
      FiniteField.pow_card_sub_one_eq_one _ (pow_ne_zero 2 (inv_ne_zero hl0)), one_smul,
      one_smul, sub_add_cancel]
    rfl
  set E := vecMulVec x ρ with hE
  have hEE : E * E = 0 := by rw [hE, vecMulVec_mul_vecMulVec, hρx, zero_smul, vecMulVec_zero]
  have hEP : E * P = 0 := by
    rw [hE, hP, vecMulVec_mul_vecMulVec, hρx, zero_smul, vecMulVec_zero]
  have hPE : P * E = E := by rw [hE, hP, vecMulVec_mul_vecMulVec, hχx, one_smul]
  have hET : E * T = l • E := by
    rw [hT, mul_add, mul_smul_comm, mul_smul_comm, mul_sub, mul_one, hEP, sub_zero, smul_zero,
      add_zero]
  have hTE : T * E = (l⁻¹ ^ 2) • E := by
    rw [hT, add_mul, smul_mul_assoc, smul_mul_assoc, sub_mul, one_mul, hPE, sub_self, smul_zero,
      zero_add]
  have hx0 : x ≠ 0 := fun h =>
    one_ne_zero (hp 0 1 (by rw [h, zero_smul, smul_zero, add_zero])).2
  have hE0 : E ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hρ0
    have := congrFun (congrFun h0 i) j
    rw [hE, vecMulVec_apply, Matrix.zero_apply] at this
    exact mul_ne_zero hi hj this
  have hNx : N *ᵥ x = 0 := by rw [hNy', vecMulVec_mulVec, hφx, MulOpposite.op_zero, zero_smul]
  have hχN : χ ᵥ* N = 0 := by rw [hNy', vecMul_vecMulVec, hχy, zero_smul]
  have hρN : ρ ᵥ* N = 0 := by rw [hNy', vecMul_vecMulVec, hρy, zero_smul]
  have hNP : N * P = 0 := by rw [hP, mul_vecMulVec, hNx, zero_vecMulVec]
  have hPN : P * N = 0 := by rw [hP, vecMulVec_mul, hχN, vecMulVec_zero]
  have hTN : T * N = N * T := by
    rw [hT, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm,
      sub_mul, mul_sub, hNP, hPN, one_mul, mul_one]
  have hEN : (1 + E) * N = N * (1 + E) := by
    rw [mul_add, add_mul, mul_one, one_mul, hE, vecMulVec_mul, hρN, vecMulVec_zero,
      mul_vecMulVec, hNx, zero_vecMulVec]
  have hNA' : ∀ g : SpecialLinearGroup (Fin n) K, (g : Matrix (Fin n) (Fin n) K) * N = N * g →
      conjAut n K A (proj n K g) = proj n K g := fun g hg =>
    conjAut_proj_eq_of_comm (by rw [← hNA]; exact hg)
  set Ti := ((τ⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hTi
  have hTTi : T * Ti = 1 := by
    rw [hTi, ← hτT, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hETi : E * Ti = l⁻¹ • E := by
    have h1 : E = l • (E * Ti) := by
      calc E = E * (T * Ti) := by rw [hTTi, mul_one]
        _ = (E * T) * Ti := by rw [mul_assoc]
        _ = l • (E * Ti) := by rw [hET, smul_mul_assoc]
    calc E * Ti = l⁻¹ • (l • (E * Ti)) := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = l⁻¹ • E := by rw [← h1]
  have hne : (τ : Matrix (Fin n) (Fin n) K) * E ≠ E * τ := by
    rw [hτT, hTE, hET]
    intro h
    have h' : (l⁻¹ ^ 2 - l) • E = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h' with h'' | h''
    · apply hl3
      have h3 : l⁻¹ ^ 2 = l := sub_eq_zero.mp h''
      calc l ^ 3 = l ^ 2 * l := by ring
        _ = l ^ 2 * l⁻¹ ^ 2 := by rw [h3]
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hl0, one_pow]
    · exact hE0 h''
  refine hasWit_of_sl h2 τ hm hτm hEE ?_ ?_ hne (hNA' τ hTN) (hNA' _ ?_)
  · rw [hτT, hET, smul_mul_assoc, hEE, smul_zero]
  · rw [← hTi, hETi, smul_mul_assoc, hEE, smul_zero]
  · rw [coe_unipOf]
    exact hEN

theorem hasWit_conjAut [Finite K] (h2 : (2 : K) = 0) (hn : 3 ≤ n)
    (h3 : n = 3 → 8 ≤ Nat.card K) {A : GL (Fin n) K} (hv : orderOf (conjAut n K A) = 2) :
    HasWit (conjAut n K A) := by
  have : Fintype K := Fintype.ofFinite K
  have hsq : conjAut n K (A * A) = 1 := by rw [map_mul, ← sq, ← hv, pow_orderOf_eq_one]
  obtain ⟨-, c, hc⟩ :=
    eq_one_of_conjAut_mul_fieldAut_eq_one hn (A * A) 1 (by rw [map_one, mul_one, hsq])
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar_eq_two h2) (c : K)
  have hAA : (A : Matrix (Fin n) (Fin n) K) * A = (c : K) • 1 := by
    rw [← Units.val_mul, ← hc, GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
    rfl
  set N := (A : Matrix (Fin n) (Fin n) K) + μ • 1 with hN
  have hNN : N * N = 0 := by
    have e : N * N = (A : Matrix (Fin n) (Fin n) K) * A +
        (μ • (A : Matrix (Fin n) (Fin n) K) + μ • A) + (μ * μ) • 1 := by
      simp only [hN, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
        smul_smul, smul_add]
      abel
    rw [e, hAA, hμ, add_self_eq_zero_of_two h2, add_zero, add_self_eq_zero_of_two h2]
  have hN0 : N ≠ 0 := by
    intro h0
    have hA : (A : Matrix (Fin n) (Fin n) K) = (-μ) • 1 := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, ← hN, h0]
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have hμ0 : -μ ≠ 0 := by
      intro hμ0
      rw [hμ0, zero_smul] at hA
      have h1 := A.mul_inv
      rw [hA, zero_mul] at h1
      exact zero_ne_one h1
    have hAs : A = GeneralLinearGroup.scalar (Fin n) (Units.mk0 (-μ) hμ0) := by
      ext i j
      rw [GeneralLinearGroup.coe_scalar, hA, smul_one_eq_diagonal]
      rfl
    rw [hAs, conjAut_scalar, orderOf_one] at hv
    omega
  by_cases hrk2 : ∃ f₁ f₂ : Fin n → K, LinearIndependent K ![N *ᵥ f₁, N *ᵥ f₂]
  · obtain ⟨f₁, f₂, hind⟩ := hrk2
    exact hasWit_of_rank_two h2 hN hNN hind
  · push Not at hrk2
    obtain ⟨f₀, φ₀, hy0, hNy, hφy⟩ := exists_rank_one hNN hN0 hrk2
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · exact hasWit_of_rank_one_three h2 (by omega) (h3 (by omega)) hN hy0 hNy hφy
    · exact hasWit_of_rank_one h2 h4 hN hy0 hNy hφy

end CFSG.ComponentClassification.HarrisLit.L33.C2
