module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherNormShell
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo

open CFSG Matrix
open CFSG.LocalAnalysis.ComponentInitial

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def vb (u : Fin n → K) : Fin n → K := fun i => h.bar (u i)

@[expose] def hf (u v : Fin n → K) : K := vb h u ⬝ᵥ v

@[expose] def adj (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := (X.map h.bar)ᵀ

@[expose] def rk (u w : Fin n → K) : Matrix (Fin n) (Fin n) K := vecMulVec u (vb h w)

theorem vb_add (u v : Fin n → K) : vb h (u + v) = vb h u + vb h v :=
  funext fun i => map_add h.bar (u i) (v i)

theorem vb_smul (c : K) (u : Fin n → K) : vb h (c • u) = h.bar c • vb h u :=
  funext fun i => map_mul h.bar c (u i)

theorem vb_zero : vb h (0 : Fin n → K) = 0 :=
  funext fun _ => map_zero h.bar

theorem vb_single (i : Fin n) : vb h (Pi.single i 1) = Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [vb]
  · simp [vb, Pi.single_eq_of_ne hj]

theorem hf_comm (u v : Fin n → K) : h.bar (hf h u v) = hf h v u := by
  simp only [hf, vb, dotProduct, map_sum, map_mul, h.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hf_add_left (u v w : Fin n → K) : hf h (u + v) w = hf h u w + hf h v w := by
  rw [hf, vb_add, add_dotProduct]
  rfl

theorem hf_add_right (u v w : Fin n → K) : hf h u (v + w) = hf h u v + hf h u w :=
  dotProduct_add _ _ _

theorem hf_smul_left (c : K) (u v : Fin n → K) : hf h (c • u) v = h.bar c * hf h u v := by
  rw [hf, vb_smul, smul_dotProduct, smul_eq_mul]
  rfl

theorem hf_smul_right (c : K) (u v : Fin n → K) : hf h u (c • v) = c * hf h u v := by
  rw [hf, dotProduct_smul, smul_eq_mul]
  rfl

theorem hf_zero_left (v : Fin n → K) : hf h 0 v = 0 := by
  rw [hf, vb_zero, zero_dotProduct]

theorem hf_zero_right (u : Fin n → K) : hf h u 0 = 0 :=
  dotProduct_zero _

theorem vb_adj_mulVec (X : Matrix (Fin n) (Fin n) K) (u : Fin n → K) :
    vb h (adj h X *ᵥ u) = vb h u ᵥ* X := by
  ext j
  simp only [vb, vecMul, mulVec, dotProduct, adj, transpose_apply, map_apply, map_sum, map_mul,
    h.bar_bar]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hf_mulVec (X : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hf h u (X *ᵥ v) = hf h (adj h X *ᵥ u) v := by
  rw [hf, hf, vb_adj_mulVec, dotProduct_mulVec]

theorem adj_adj (X : Matrix (Fin n) (Fin n) K) : adj h (adj h X) = X := by
  ext i j
  simp [adj, h.bar_bar]

theorem hf_mulVec_left (X : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hf h (X *ᵥ u) v = hf h u (adj h X *ᵥ v) := by
  rw [hf_mulVec, adj_adj]

theorem adj_add (X Y : Matrix (Fin n) (Fin n) K) : adj h (X + Y) = adj h X + adj h Y := by
  ext i j
  simp [adj]

theorem adj_sub (X Y : Matrix (Fin n) (Fin n) K) : adj h (X - Y) = adj h X - adj h Y := by
  ext i j
  simp [adj]

theorem adj_smul (c : K) (X : Matrix (Fin n) (Fin n) K) : adj h (c • X) = h.bar c • adj h X := by
  ext i j
  simp [adj]

theorem adj_one : adj h (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [adj, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one]

theorem adj_mul (X Y : Matrix (Fin n) (Fin n) K) : adj h (X * Y) = adj h Y * adj h X := by
  rw [adj, adj, adj, Matrix.map_mul, transpose_mul]

theorem rk_mulVec (u w v : Fin n → K) : rk h u w *ᵥ v = hf h w v • u := by
  ext i
  simp only [rk, hf, mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem rk_mul_rk (a b c d : Fin n → K) : rk h a b * rk h c d = hf h b c • rk h a d := by
  rw [rk, rk, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  rfl

theorem mul_rk (X : Matrix (Fin n) (Fin n) K) (u w : Fin n → K) :
    X * rk h u w = rk h (X *ᵥ u) w :=
  mul_vecMulVec X u (vb h w)

theorem rk_mul (X : Matrix (Fin n) (Fin n) K) (u w : Fin n → K) :
    rk h u w * X = rk h u (adj h X *ᵥ w) := by
  rw [rk, rk, vecMulVec_mul, vb_adj_mulVec]

theorem adj_rk (u w : Fin n → K) : adj h (rk h u w) = rk h w u := by
  ext i j
  simp only [adj, rk, vb, transpose_apply, map_apply, vecMulVec_apply, map_mul, h.bar_bar]
  exact mul_comm _ _

theorem rk_zero_left (w : Fin n → K) : rk h 0 w = 0 :=
  zero_vecMulVec _

theorem rk_zero_right (u : Fin n → K) : rk h u 0 = 0 := by
  rw [rk, vb_zero, vecMulVec_zero]

theorem det_one_add_smul_rk (c : K) (u w : Fin n → K) :
    (1 + c • rk h u w).det = 1 + c * hf h w u := by
  rw [rk, ← smul_vecMulVec, vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, smul_eq_mul]
  rfl

theorem exists_hf_ne_zero {M : Matrix (Fin n) (Fin n) K} (hM : adj h M = M) (hM0 : M ≠ 0) :
    ∃ x, hf h x (M *ᵥ x) ≠ 0 := by
  by_contra! hz
  apply hM0
  have hpol : ∀ x y : Fin n → K, hf h x (M *ᵥ y) + h.bar (hf h x (M *ᵥ y)) = 0 := by
    intro x y
    have h1 := hz (x + y)
    rw [mulVec_add, hf_add_left, hf_add_right, hf_add_right, hz x, hz y, zero_add, add_zero,
      hf_mulVec h M y x, hM, ← hf_comm h x (M *ᵥ y)] at h1
    exact h1
  have hzero : ∀ x y : Fin n → K, hf h x (M *ᵥ y) = 0 := by
    intro x y
    by_contra ht
    obtain ⟨d, hd⟩ := UnitaryFieldData.exists_trace_ne_zero h
    apply hd
    have h1 := hpol (h.bar (d * (hf h x (M *ᵥ y))⁻¹) • x) y
    rwa [hf_smul_left, h.bar_bar, mul_assoc, inv_mul_cancel₀ ht, mul_one] at h1
  ext i j
  have h1 := hzero (Pi.single i 1) (Pi.single j 1)
  rwa [hf, vb_single, single_dotProduct, one_mul, mulVec_single_one] at h1

theorem bar_hf_self (u : Fin n → K) : h.bar (hf h u u) = hf h u u :=
  hf_comm h u u

theorem exists_hyp {N : Matrix (Fin n) (Fin n) K} (hN : adj h N = N) (hNN : N * N = 0)
    {x₀ : Fin n → K} (hx₀ : hf h x₀ (N *ᵥ x₀) ≠ 0) :
    ∃ x : Fin n → K, hf h x (N *ᵥ x) = 1 ∧ hf h x x = 0 ∧
      ∃ l t : K, x = l • x₀ + t • (N *ᵥ x₀) := by
  have : CharP K 2 := h.charP
  have hNNv : ∀ v : Fin n → K, N *ᵥ (N *ᵥ v) = 0 := fun v => by
    rw [mulVec_mulVec, hNN, zero_mulVec]
  have hsym : ∀ u v : Fin n → K, hf h (N *ᵥ u) v = hf h u (N *ᵥ v) := fun u v => by
    rw [hf_mulVec_left, hN]
  obtain ⟨c₀, hc₀⟩ : ∃ c, c = hf h x₀ (N *ᵥ x₀) := ⟨_, rfl⟩
  rw [← hc₀] at hx₀
  have hbc₀ : h.bar c₀ = c₀ := by rw [hc₀, hf_comm, hsym]
  obtain ⟨l, hl⟩ := UnitaryHigher.exists_norm_eq h (c := c₀⁻¹) (by rw [map_inv₀, hbc₀])
  rw [UnitaryFieldData.norm] at hl
  obtain ⟨x₁, hx₁⟩ : ∃ x, x = l • x₀ := ⟨_, rfl⟩
  have hx₁N : hf h x₁ (N *ᵥ x₁) = 1 := by
    rw [hx₁, mulVec_smul, hf_smul_left, hf_smul_right, ← hc₀, ← mul_assoc, mul_comm (h.bar l),
      hl, inv_mul_cancel₀ hx₀]
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = N *ᵥ x₁ := ⟨_, rfl⟩
  rw [← hy₁] at hx₁N
  have hNy₁ : N *ᵥ y₁ = 0 := by rw [hy₁, hNNv]
  have hy₁y₁ : hf h y₁ y₁ = 0 := by rw [hy₁, hsym, hNNv, hf_zero_right]
  have hy₁x₁ : hf h y₁ x₁ = 1 := by rw [← hf_comm, hx₁N, map_one]
  obtain ⟨d₁, hd₁⟩ : ∃ d, d = hf h x₁ x₁ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := UnitaryFieldData.exists_trace_ne_zero h
  rw [UnitaryFieldData.trace] at hc
  have hbτ : h.bar (c + h.bar c) = c + h.bar c := by rw [map_add, h.bar_bar, add_comm]
  obtain ⟨t, ht⟩ : ∃ t, t = c * (d₁ * (c + h.bar c)⁻¹) := ⟨_, rfl⟩
  have htt : t + h.bar t = d₁ := by
    rw [ht, map_mul, map_mul, map_inv₀, hbτ, hd₁, bar_hf_self, ← add_mul,
      mul_comm (hf h x₁ x₁), ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine ⟨x₁ + t • y₁, ?_, ?_, l, t * l, ?_⟩
  · rw [mulVec_add, mulVec_smul, hNy₁, smul_zero, add_zero, ← hy₁, hf_add_left, hf_smul_left,
      hy₁y₁, mul_zero, add_zero, hx₁N]
  · rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_right, hf_smul_left,
      hf_smul_right, hy₁y₁, hy₁x₁, hx₁N, ← hd₁, mul_one, mul_one, mul_zero, mul_zero,
      add_zero, add_assoc, htt, CharTwo.add_self_eq_zero]
  · rw [hy₁, hx₁, mulVec_smul, smul_smul]

theorem exists_unit {w₀ : Fin n → K} (hw₀ : hf h w₀ w₀ ≠ 0) :
    ∃ l : K, hf h (l • w₀) (l • w₀) = 1 := by
  obtain ⟨l, hl⟩ := UnitaryHigher.exists_norm_eq h (c := (hf h w₀ w₀)⁻¹)
    (by rw [map_inv₀, bar_hf_self])
  rw [UnitaryFieldData.norm] at hl
  refine ⟨l, ?_⟩
  rw [hf_smul_left, hf_smul_right, ← mul_assoc, mul_comm (h.bar l), hl, inv_mul_cancel₀ hw₀]

theorem exists_orth {m : ℕ} (hm : m < n) (u : Fin m → Fin n → K) :
    ∃ v : Fin n → K, v ≠ 0 ∧ ∀ i, hf h (u i) v = 0 := by
  set M : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => if hi : (i : ℕ) < m then vb h (u ⟨i, hi⟩) j else 0 with hM
  have hdet : M.det = 0 :=
    det_eq_zero_of_row_eq_zero ⟨m, hm⟩ fun j => by simp [hM]
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, fun i => ?_⟩
  have h1 := congrFun hv ⟨i, lt_trans i.2 hm⟩
  simpa [hM, mulVec, dotProduct, hf] using h1

end CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo
