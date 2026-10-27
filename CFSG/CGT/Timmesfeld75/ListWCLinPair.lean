module

public import CFSG.CGT.Timmesfeld75.ListWCLinBasic
public import CFSG.CGT.Timmesfeld75.WCBasic

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

variable {K : Type*} [Field K] {m : ℕ}

theorem exists_dot_of_notMem {S : Submodule K (Fin m → K)} {d : Fin m → K} (hd : d ∉ S) :
    ∃ χ : Fin m → K, (∀ v ∈ S, χ ⬝ᵥ v = 0) ∧ χ ⬝ᵥ d = 1 := by
  obtain ⟨f, hfd, hS⟩ := Submodule.exists_le_ker_of_notMem hd
  let χ₀ : Fin m → K := fun i => f fun j => if i = j then 1 else 0
  have hf : ∀ v, f v = χ₀ ⬝ᵥ v := fun v => by
    rw [LinearMap.pi_apply_eq_sum_univ f v, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  refine ⟨(f d)⁻¹ • χ₀, fun v hv => ?_, ?_⟩
  · rw [smul_dotProduct, ← hf, LinearMap.mem_ker.1 (hS hv), smul_zero]
  · rw [smul_dotProduct, ← hf, smul_eq_mul, inv_mul_cancel₀ hfd]

theorem exists_dot_of_not_smul {c d : Fin m → K} (hdc : ∀ μ : K, d ≠ μ • c) :
    ∃ χ : Fin m → K, χ ⬝ᵥ c = 0 ∧ χ ⬝ᵥ d = 1 := by
  obtain ⟨χ, h0, h1⟩ := exists_dot_of_notMem (S := K ∙ c) (d := d) (by
    rw [Submodule.mem_span_singleton]
    rintro ⟨μ, hμ⟩
    exact hdc μ hμ.symm)
  exact ⟨χ, h0 c (Submodule.mem_span_singleton_self c), h1⟩

theorem exists_dot_of_not_mem_pair {c e d : Fin m → K}
    (hd : ∀ α β : K, d ≠ α • c + β • e) :
    ∃ θ : Fin m → K, θ ⬝ᵥ c = 0 ∧ θ ⬝ᵥ e = 0 ∧ θ ⬝ᵥ d = 1 := by
  obtain ⟨θ, h0, h1⟩ := exists_dot_of_notMem (S := Submodule.span K {c, e}) (d := d) (by
    rw [Submodule.mem_span_pair]
    rintro ⟨α, β, h⟩
    exact hd α β h.symm)
  exact ⟨θ, h0 c (Submodule.subset_span (by simp)), h0 e (Submodule.subset_span (by simp)), h1⟩

theorem vecMulVec_mulVec' (c a v : Fin m → K) : vecMulVec c a *ᵥ v = (a ⬝ᵥ v) • c := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

theorem one_add_vecMulVec_mulVec (c a d : Fin m → K) :
    (1 + vecMulVec c a) *ᵥ d = d + (a ⬝ᵥ d) • c := by
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec']

theorem vecMul_one_sub_vecMulVec (ψ c a : Fin m → K) :
    ψ ᵥ* (1 - vecMulVec c a) = ψ - (ψ ⬝ᵥ c) • a := by
  rw [vecMul_sub, vecMul_one, vecMul_vecMulVec]

theorem coe_mul_comm_of_mul_comm {x y : SL(m, K)} (h : x * y = y * x) :
    (x : Matrix (Fin m) (Fin m) K) * (y : Matrix (Fin m) (Fin m) K) =
      (y : Matrix (Fin m) (Fin m) K) * (x : Matrix (Fin m) (Fin m) K) := by
  have := congrArg (fun z : SL(m, K) => (z : Matrix (Fin m) (Fin m) K)) h
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using this

theorem tv_mul_tv_center {c a b : Fin m → K} (ha : a ⬝ᵥ c = 0) :
    (1 + vecMulVec c a) * (1 + vecMulVec c b) = 1 + vecMulVec c (a + b) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, vecMulVec_mul_vecMulVec, ha, zero_smul, vecMulVec_zero, add_zero,
    vecMulVec_add]
  abel

theorem tv_mul_tv_axis {a v w : Fin m → K} (hw : a ⬝ᵥ w = 0) :
    (1 + vecMulVec v a) * (1 + vecMulVec w a) = 1 + vecMulVec (v + w) a := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, vecMulVec_mul_vecMulVec, hw, zero_smul, vecMulVec_zero, add_zero,
    add_vecMulVec]
  abel

variable [CharP K 2]

theorem vec_add_self' (v : Fin m → K) : v + v = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (v i)

theorem fix_of_commute_tv {x t : SL(m, K)} {c φ : Fin m → K} (hc : c ≠ 0) (hφ : φ ≠ 0)
    (ht : (t : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c φ) (hxt : x * t = t * x)
    (hx : x * x = 1) :
    (x : Matrix (Fin m) (Fin m) K) *ᵥ c = c ∧ φ ᵥ* (x : Matrix (Fin m) (Fin m) K) = φ := by
  set X := (x : Matrix (Fin m) (Fin m) K) with hX
  have h1 : X * (1 + vecMulVec c φ) = (1 + vecMulVec c φ) * X := by
    have := congrArg (fun y : SL(m, K) => (y : Matrix (Fin m) (Fin m) K)) hxt
    simpa only [Matrix.SpecialLinearGroup.coe_mul, ht] using this
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
  have h2 := add_left_cancel h1
  rw [mul_vecMulVec, vecMulVec_mul] at h2
  obtain ⟨μ, hμc, hμφ⟩ := exists_smul_of_vecMulVec_eq h2 hc hφ
  have hXX : X * X = 1 := by
    have := congrArg (fun y : SL(m, K) => (y : Matrix (Fin m) (Fin m) K)) hx
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using this
  have hμ : μ * μ = 1 := by
    have h3 : X *ᵥ (X *ᵥ c) = c := by rw [mulVec_mulVec, hXX, one_mulVec]
    rw [hμc, mulVec_smul, hμc, smul_smul] at h3
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
    have h4 := congrFun h3 i
    simp only [Pi.smul_apply, smul_eq_mul] at h4
    have hi' : c i ≠ 0 := by simpa using hi
    exact mul_right_cancel₀ hi' (by rw [h4, one_mul])
  have hμ1 := eq_one_of_mul_self_eq_one_char_two hμ
  rw [hμ1, one_smul] at hμc hμφ
  exact ⟨hμc, hμφ⟩

theorem false_of_two_tv {T : Subgroup SL(m, K)} (hT : IsWC T) {t s : SL(m, K)} (htT : t ∈ T)
    (hsT : s ∈ T) {c φ d ψ : Fin m → K}
    (ht : (t : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c φ)
    (hs : (s : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec d ψ)
    (hc : c ≠ 0) (hφ : φ ≠ 0) (hφc : φ ⬝ᵥ c = 0) (hd : d ≠ 0) (hψ : ψ ≠ 0) (hψd : ψ ⬝ᵥ d = 0)
    (hdc : ∀ μ : K, d ≠ μ • c) (hψφ : ∀ μ : K, ψ ≠ μ • φ) : False := by
  have hcomm : ∀ {x y : SL(m, K)}, x ∈ T → y ∈ T → x * y = y * x := fun hx hy =>
    elemAbelian_mul_comm hT.1 hx hy
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply vecMulVec_ne_zero_of hc hφ
    have h := ht.symm
    rw [Matrix.SpecialLinearGroup.coe_one] at h
    simpa using h
  have hN : ∀ g : SL(m, K), g * t = t * g → ∀ y ∈ T, g * y * g⁻¹ ∈ T := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.1 (hT.centralizer_le_normalizer htT ht1
      (Subgroup.mem_centralizer_singleton_iff.2 hg)) y).1 hy
  obtain ⟨hφd, hψc⟩ := dotProduct_eq_zero_of_commute hc hd hφ hψ hdc (by
    rw [← ht, ← hs]
    exact coe_mul_comm_of_mul_comm (hcomm htT hsT))
  obtain ⟨χ, hχc, hχd⟩ := exists_dot_of_not_smul hdc
  let τ := tvSL c χ hχc
  have hτt : τ * t = t * τ := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, ht,
      tv_mul_tv_center hχc, tv_mul_tv_center hφc, add_comm χ φ])
  have hs₁ : ((τ * s * τ⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec (d + c) ψ := by
    rw [coe_conj_of_coe τ hs, coe_tvSL, one_add_vecMulVec_mulVec, hχd, one_smul, coe_tvSL_inv,
      vecMul_one_sub_vecMulVec, hψc, zero_smul, sub_zero]
  have hr : ((s * (τ * s * τ⁻¹) : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec c ψ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hs, hs₁, tv_mul_tv_axis (by
      rw [dotProduct_add, hψd, hψc, add_zero]), ← add_assoc, vec_add_self', zero_add]
  have hrT : s * (τ * s * τ⁻¹) ∈ T := T.mul_mem hsT (hN τ hτt s hsT)
  obtain ⟨w, hwφ, hwψ⟩ := exists_dot_of_not_smul hψφ
  rw [dotProduct_comm] at hwφ hwψ
  let τ' := tvSL w φ hwφ
  have hτ't : τ' * t = t * τ' := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, ht,
      tv_mul_tv_axis hφc, tv_mul_tv_axis hwφ, add_comm w c])
  have hs₂ : ((τ' * s * τ'⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec d (ψ - φ) := by
    rw [coe_conj_of_coe τ' hs, coe_tvSL, one_add_vecMulVec_mulVec, hφd, zero_smul, add_zero,
      coe_tvSL_inv, vecMul_one_sub_vecMulVec, hwψ, one_smul]
  have hu : ((s * (τ' * s * τ'⁻¹) : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec d φ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hs, hs₂, tv_mul_tv_center hψd, ← add_sub_assoc,
      vec_add_self', zero_sub, neg_eq_of_add_eq_zero_left (vec_add_self' φ)]
  have huT : s * (τ' * s * τ'⁻¹) ∈ T := T.mul_mem hsT (hN τ' hτ't s hsT)
  obtain ⟨θ, hθc, hθw, hθd⟩ := exists_dot_of_not_mem_pair (c := c) (e := w) (d := d)
    (fun α β h => by
      have h1 := congrArg (fun v => ψ ⬝ᵥ v) h
      simp only [dotProduct_add, dotProduct_smul, hψc, hwψ, smul_eq_mul, mul_zero, mul_one,
        zero_add, hψd] at h1
      apply hdc α
      rw [h, ← h1, zero_smul, add_zero])
  let g := tvSL w θ hθw
  have hgt : g * t = t * g := by
    have h1 : g * t * g⁻¹ = t := Subtype.ext (by
      rw [coe_conj_of_coe g ht, coe_tvSL, one_add_vecMulVec_mulVec, hθc, zero_smul, add_zero,
        coe_tvSL_inv, vecMul_one_sub_vecMulVec, hwφ, zero_smul, sub_zero, ht])
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]
  have hr' : ((g * (s * (τ * s * τ⁻¹)) * g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec c (ψ - θ) := by
    rw [coe_conj_of_coe g hr, coe_tvSL, one_add_vecMulVec_mulVec, hθc, zero_smul, add_zero,
      coe_tvSL_inv, vecMul_one_sub_vecMulVec, hwψ, one_smul]
  have hr'T := hN g hgt _ hrT
  have hval : (ψ - θ) ⬝ᵥ d = -1 := by rw [sub_dotProduct, hψd, hθd, zero_sub]
  have hψθ : ψ - θ ≠ 0 := fun h => by
    rw [h, zero_dotProduct] at hval
    exact one_ne_zero (neg_eq_zero.1 hval.symm)
  obtain ⟨h0, -⟩ := dotProduct_eq_zero_of_commute hc hd hψθ hφ hdc (by
    rw [← hr', ← hu]
    exact coe_mul_comm_of_mul_comm (hcomm hr'T huT))
  rw [hval] at h0
  exact one_ne_zero (neg_eq_zero.1 h0)

theorem exists_commute_move {N : Matrix (Fin m) (Fin m) K} (hN : N * N = 0) {c v₀ : Fin m → K}
    (hc : c ≠ 0) (hNc : N *ᵥ c = 0) (hv₀ : ∀ μ : K, N *ᵥ v₀ ≠ μ • c) :
    ∃ g : SL(m, K), (g : Matrix (Fin m) (Fin m) K) * N = N * (g : Matrix (Fin m) (Fin m) K) ∧
      ∀ μ : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ c ≠ μ • c := by
  have hu0 : N *ᵥ v₀ ≠ 0 := fun h => hv₀ 0 (by rw [h, zero_smul])
  have hNu : N *ᵥ (N *ᵥ v₀) = 0 := by rw [mulVec_mulVec, hN, zero_mulVec]
  obtain ⟨θ, hθu, hθv, hθc⟩ := exists_dot_of_not_mem_pair (c := N *ᵥ v₀) (e := v₀) (d := c)
    (fun α β h => by
      have h1 := congrArg (fun v => N *ᵥ v) h
      simp only [mulVec_add, mulVec_smul, hNc, hNu, smul_zero, zero_add] at h1
      have hβ : β = 0 := by
        by_contra hβ
        exact hu0 ((smul_eq_zero.1 h1.symm).resolve_left hβ)
      rw [hβ, zero_smul, add_zero] at h
      have hα : α ≠ 0 := by
        rintro rfl
        rw [zero_smul] at h
        exact hc h
      apply hv₀ α⁻¹
      rw [h, smul_smul, inv_mul_cancel₀ hα, one_smul])
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin m) (Fin m) K,
      E = vecMulVec (N *ᵥ v₀) θ + vecMulVec v₀ (θ ᵥ* N) := ⟨_, rfl⟩
  have hθN : ∀ x, (θ ᵥ* N) ⬝ᵥ x = θ ⬝ᵥ (N *ᵥ x) := fun x => (dotProduct_mulVec θ N x).symm
  have hEN : E * N = N * E := by
    rw [hE, Matrix.add_mul, Matrix.mul_add, vecMulVec_mul, vecMulVec_mul, mul_vecMulVec,
      mul_vecMulVec, vecMul_vecMul, hN, vecMul_zero, vecMulVec_zero, add_zero, hNu,
      zero_vecMulVec, zero_add]
  have hEE : E * E = 0 := by
    rw [hE, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, vecMulVec_mul_vecMulVec,
      vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, hθu, hθv,
      hθN, hθN, hNu, dotProduct_zero, hθu]
    simp
  have hgg : (1 + E) * (1 + E) = 1 := by
    have e : (1 + E) * (1 + E) = 1 + (E + E) + E * E := by noncomm_ring
    rw [e, hEE, add_self_eq_zero_matrix, add_zero, add_zero]
  refine ⟨⟨1 + E, det_eq_one_of_mul_self hgg⟩, ?_, fun μ hμ => ?_⟩
  · show (1 + E) * N = N * (1 + E)
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hEN]
  · have h1 : (1 + E) *ᵥ c = c + N *ᵥ v₀ := by
      rw [hE, add_mulVec, add_mulVec, one_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', hθc,
        hθN, hNc, dotProduct_zero, zero_smul, add_zero, one_smul]
    have hμ' : (1 + E) *ᵥ c = μ • c := hμ
    rw [h1] at hμ'
    apply hv₀ (μ - 1)
    rw [sub_smul, one_smul, ← hμ', add_sub_cancel_left]

theorem exists_commute_move' {N : Matrix (Fin m) (Fin m) K} (hN : N * N = 0)
    {φ w₀ : Fin m → K} (hφ : φ ≠ 0) (hNφ : φ ᵥ* N = 0) (hw₀ : ∀ μ : K, w₀ ᵥ* N ≠ μ • φ) :
    ∃ g : SL(m, K), (g : Matrix (Fin m) (Fin m) K) * N = N * (g : Matrix (Fin m) (Fin m) K) ∧
      ∀ μ : K, φ ᵥ* (g : Matrix (Fin m) (Fin m) K) ≠ μ • φ := by
  obtain ⟨g, hgN, hgc⟩ := exists_commute_move (N := Nᵀ)
    (by rw [← transpose_mul, hN, transpose_zero]) hφ (by rw [mulVec_transpose, hNφ])
    (fun μ => by rw [mulVec_transpose]; exact hw₀ μ)
  refine ⟨Matrix.SpecialLinearGroup.transpose g, ?_, fun μ => ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_transpose]
    have := congrArg Matrix.transpose hgN
    rw [transpose_mul, transpose_mul, transpose_transpose] at this
    exact this.symm
  · rw [Matrix.SpecialLinearGroup.coe_transpose, vecMul_transpose]
    exact hgc μ

end CFSG.CGT.Timmesfeld75
