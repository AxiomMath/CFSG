module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteCross

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

namespace Frame

variable {I H K : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype K]
  {d : I → ℤ} {A : H → I → ℤ} {E : K → I → ℤ} {Ys : I → ℤ} {Y : K → I → ℤ} {C : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : H → I} {q : K → Fin 4 → I} {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
  {η : K → Fin 4 → ℤ} {D : ℤ}

section Generic

variable (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
include F

omit [Fintype I] [DecidableEq I] [Fintype H] [Fintype K] F in
theorem pair_sum_of {k : K} {w : I → ℤ}
    (h01 : η k 0 * w (q k 0) + η k 1 * w (q k 1) = 0)
    (h23 : η k 2 * w (q k 2) + η k 3 * w (q k 3) = 0) (e : Fin 2) :
    η k (pairA e) * w (q k (pairA e)) + η k (pairB e) * w (q k (pairB e)) = 0 := by
  fin_cases e
  · exact h01
  · exact h23

omit [Fintype I] [Fintype H] [Fintype K] in
theorem sum_sq_q_of {k : K} {w : I → ℤ}
    (h01 : η k 0 * w (q k 0) + η k 1 * w (q k 1) = 0)
    (h23 : η k 2 * w (q k 2) + η k 3 * w (q k 3) = 0) (e : Fin 2) :
    ∑ l, w (q k l) * w (q k l) =
      2 * ((η k (pairA e) * w (q k (pairA e))) * (η k (pairA e) * w (q k (pairA e)))) +
      2 * ((η k (pairA (1 - e)) * w (q k (pairA (1 - e)))) *
        (η k (pairA (1 - e)) * w (q k (pairA (1 - e))))) := by
  have hsq : ∀ l, (η k l * w (q k l)) * (η k l * w (q k l)) = w (q k l) * w (q k l) := by
    intro l
    have h := sign_mul_self (F.sη k l)
    linear_combination (w (q k l) * w (q k l)) * h
  have e1 : w (q k 1) * w (q k 1) = w (q k 0) * w (q k 0) := by
    rw [← hsq 0, ← hsq 1, show η k 1 * w (q k 1) = -(η k 0 * w (q k 0)) by linarith]
    ring
  have e3 : w (q k 3) * w (q k 3) = w (q k 2) * w (q k 2) := by
    rw [← hsq 2, ← hsq 3, show η k 3 * w (q k 3) = -(η k 2 * w (q k 2)) by linarith]
    ring
  rw [Fin.sum_univ_four, e1, e3]
  fin_cases e
  · simp only [pairA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sub_zero,
      Matrix.cons_val_one]
    rw [hsq 0, hsq 2]
    ring
  · simp only [pairA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, sub_self,
      Matrix.cons_val_zero]
    rw [hsq 0, hsq 2]
    ring

omit [Fintype K] in
theorem generic_caseA (hH : 2 ≤ Fintype.card H) (k : K) {w c c' : I → ℤ} {ξ : I}
    {ϑ σ σ' : ℤ} {e : Fin 2} (hϑ : ϑ = 1 ∨ ϑ = -1) (hσ : σ = 1 ∨ σ = -1)
    (hσ' : σ' = 1 ∨ σ' = -1) (hc : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k c 0 ξ ϑ)
    (hcp : PairAt (q k) (η k) c e σ)
    (hc' : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k c' 0 ξ ϑ)
    (hc'p : PairAt (q k) (η k) c' (1 - e) σ') (hww : w ⬝ᵥ w = 7) (hwA : ∀ h, w ⬝ᵥ A h = 0)
    (hwYs : w ⬝ᵥ Ys = 0) (hwC : w ⬝ᵥ C = 6) (hwE : w ⬝ᵥ E k = 0) (hwY : w ⬝ᵥ Y k = 0)
    (hwc : w ⬝ᵥ c = 6) (hwc' : w ⬝ᵥ c' = 6) : w ξ = ϑ := by
  have hs2nn : 0 ≤ ∑ l, w (q k l) * w (q k l) := Finset.sum_nonneg fun l _ => mul_self_nonneg _
  obtain ⟨-, h01, h23, b, w0, w1, w2, w3, w4, hR⟩ :=
    F.column_shape hH k hwA hwYs hwC hwE hwY (by rw [hww]; linarith)
  have hcoreW : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ b w := ⟨w0, w1, w2, w3, w4⟩
  have hϑ0 : ϑ ≠ 0 := by rcases hϑ with h | h <;> rw [h] <;> norm_num
  have hd1 := F.dot_pair_column hc hcp hcoreW (pair_sum_of h01 h23 e)
  have hd2 := F.dot_pair_column hc' hc'p hcoreW (pair_sum_of h01 h23 (1 - e))
  rw [hwc] at hd1
  rw [hwc'] at hd2
  have hξ : ξ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k) := (hc.2.2.2 hϑ0).1
  have hξle : w ξ * w ξ ≤ ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i * w i :=
    Finset.single_le_sum (f := fun i => w i * w i) (fun i _ => mul_self_nonneg (w i)) hξ
  have hs2 := F.sum_sq_q_of h01 h23 e
  rw [hww] at hR
  have hb : ((if b = 0 then caseNorm b else 4) = 5 ∧ 7 - caseNorm b = 2) ∨
      ((if b = 0 then caseNorm b else 4) = 4 ∧ 7 - caseNorm b = 1) := by
    fin_cases b <;> simp [caseNorm]
  have hn : 2 * ((η k (pairA e) * w (q k (pairA e))) * (η k (pairA e) * w (q k (pairA e)))) +
      2 * ((η k (pairA (1 - e)) * w (q k (pairA (1 - e)))) *
        (η k (pairA (1 - e)) * w (q k (pairA (1 - e))))) + w ξ * w ξ ≤ 7 - caseNorm b := by
    linarith
  exact (generic_caseA_scalar hσ hσ' hϑ hb (by linarith) (by linarith) hn).2

omit [Fintype K] in
theorem generic_caseB (hH : 2 ≤ Fintype.card H) (k : K) {w c c' : I → ℤ} {ξ ξ' : I}
    {σ σ' : ℤ} {e : Fin 2} (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1)
    (hc : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k c 1 ξ 0)
    (hcp : PairAt (q k) (η k) c e σ)
    (hc' : OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k c' 1 ξ' 0)
    (hc'p : PairAt (q k) (η k) c' (1 - e) σ') (hww : w ⬝ᵥ w = 7) (hwA : ∀ h, w ⬝ᵥ A h = 0)
    (hwYs : w ⬝ᵥ Ys = 0) (hwC : w ⬝ᵥ C = 6) (hwE : w ⬝ᵥ E k = 0) (hwY : w ⬝ᵥ Y k = 0)
    (hwc : w ⬝ᵥ c = 6) (hwc' : w ⬝ᵥ c' = 6) :
    CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 1 w ∧ (∀ h, w (p h) = 0) ∧ (∀ l, w (q k l) = 0) ∧
      ∃ ψ γ, (γ = 1 ∨ γ = -1) ∧ ψ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k) ∧ w ψ = γ ∧
        ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i = if i = ψ then γ else 0 := by
  have hs2nn : 0 ≤ ∑ l, w (q k l) * w (q k l) := Finset.sum_nonneg fun l _ => mul_self_nonneg _
  obtain ⟨hwp, h01, h23, b, w0, w1, w2, w3, w4, hR⟩ :=
    F.column_shape hH k hwA hwYs hwC hwE hwY (by rw [hww]; linarith)
  have hcoreW : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ b w := ⟨w0, w1, w2, w3, w4⟩
  have hd1 := F.dot_pair_column hc hcp hcoreW (pair_sum_of h01 h23 e)
  have hd2 := F.dot_pair_column hc' hc'p hcoreW (pair_sum_of h01 h23 (1 - e))
  rw [hwc, zero_mul, add_zero] at hd1
  rw [hwc', zero_mul, add_zero] at hd2
  have hs2 := F.sum_sq_q_of h01 h23 e
  have hRnn : 0 ≤ ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i * w i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [hww] at hR
  have hb : ((if b = 1 then caseNorm b else 4) = 6 ∧ 7 - caseNorm b = 1) ∨
      ((if b = 1 then caseNorm b else 4) = 4 ∧ 7 - caseNorm b ≤ 2) := by
    fin_cases b <;> simp [caseNorm]
  obtain ⟨hs6, hu, hu'⟩ := generic_caseB_scalar (u := η k (pairA e) * w (q k (pairA e)))
    (u' := η k (pairA (1 - e)) * w (q k (pairA (1 - e)))) hσ hσ' hb (by linarith)
    (by linarith) (by linarith)
  have hb1 : b = 1 := by
    by_contra hne
    rw [ite_eq_right hne] at hs6
    norm_num at hs6
  subst hb1
  have hrec : ∀ l, η k l * w (q k l) = 0 → w (q k l) = 0 := by
    intro l h
    rcases F.sη k l with h' | h' <;> rw [h'] at h <;> linarith
  have hq0 : ∀ e' : Fin 2, η k (pairA e') * w (q k (pairA e')) = 0 →
      ∀ l, (l = pairA e' ∨ l = pairB e') → w (q k l) = 0 := by
    intro e' he' l hl
    have hs := pair_sum_of h01 h23 e'
    rcases hl with rfl | rfl
    · exact hrec _ he'
    · exact hrec _ (by linarith)
  have hq : ∀ l, w (q k l) = 0 := by
    intro l
    have hall : ∀ (e : Fin 2) (l : Fin 4), (l = pairA e ∨ l = pairB e) ∨
        (l = pairA (1 - e) ∨ l = pairB (1 - e)) := by decide
    rcases hall e l with hl | hl
    · exact hq0 e hu l hl
    · exact hq0 (1 - e) hu' l hl
  have hs20 : ∑ l, w (q k l) * w (q k l) = 0 :=
    Finset.sum_eq_zero fun l _ => by rw [hq l, mul_zero]
  have hR1 : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i * w i = 1 := by
    rw [hR, hs20]
    simp [caseNorm]
  obtain ⟨ψ, hψ, hψv, hrest⟩ := exists_unit_of_sum_mul_self_eq_one hR1
  refine ⟨hcoreW, hwp, hq, ψ, w ψ, hψv, hψ, rfl, fun i hi => ?_⟩
  by_cases hiψ : i = ψ
  · rw [ite_eq_left hiψ, hiψ]
  · rw [ite_eq_right hiψ, hrest i hi hiψ]

omit [Fintype K] in
theorem dot_generic (k : K) {w w' : I → ℤ} {ψ ψ' : I} {γ γ' : ℤ}
    (hw : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 1 w) (hwp : ∀ h, w (p h) = 0)
    (hwq : ∀ l, w (q k l) = 0) (hψ : ψ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k))
    (hwv : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i = if i = ψ then γ else 0)
    (hw' : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 1 w')
    (hw'v : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w' i = if i = ψ' then γ' else 0) :
    w ⬝ᵥ w' = 6 + γ * (if ψ = ψ' then γ' else 0) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := hw
  obtain ⟨u0, u1, u2, u3, u4⟩ := hw'
  have hsplit := F.sum_split k fun i => w i * w' i
  have hvw : w ⬝ᵥ w' = ∑ i, w i * w' i := rfl
  have hodd : ∑ h, w (p h) * w' (p h) = 0 :=
    Finset.sum_eq_zero fun h _ => by rw [hwp h, zero_mul]
  have hq : ∑ l, w (q k l) * w' (q k l) = 0 :=
    Finset.sum_eq_zero fun l _ => by rw [hwq l, zero_mul]
  have hrest : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i * w' i =
      γ * (if ψ = ψ' then γ' else 0) := by
    rw [Finset.sum_eq_single ψ (fun i hi hiψ => by rw [hwv i hi, ite_eq_right hiψ, zero_mul])
      (fun h => absurd hψ h), hwv ψ hψ, ite_eq_left rfl, hw'v ψ hψ]
  have s₀ := sign_mul_self F.sδ₀
  have s₁ := sign_mul_self F.sδ₁
  have s₄ := sign_mul_self F.sδ₄
  rw [hvw, hsplit, hodd, hq, hrest, v0, v1, v2, v3, v4, u0, u1, u2, u3, u4]
  simp only [caseZ0, caseZ2, caseW, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  linear_combination s₀ + s₁ + 4 * s₄

omit [Fintype K] in
theorem degree_generic (k : K) {w : I → ℤ} {ψ : I} {γ : ℤ}
    (hw : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 1 w) (hwp : ∀ h, w (p h) = 0)
    (hwq : ∀ l, w (q k l) = 0) (hψ : ψ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k))
    (hwv : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i = if i = ψ then γ else 0) :
    w ⬝ᵥ d = δ₀ * d i₀ - δ₁ * d i₁ + 2 * δ₄ * d i₄ + γ * d ψ := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := hw
  have hsplit := F.sum_split k fun i => w i * d i
  have hvw : w ⬝ᵥ d = ∑ i, w i * d i := rfl
  have hodd : ∑ h, w (p h) * d (p h) = 0 :=
    Finset.sum_eq_zero fun h _ => by rw [hwp h, zero_mul]
  have hq : ∑ l, w (q k l) * d (q k l) = 0 :=
    Finset.sum_eq_zero fun l _ => by rw [hwq l, zero_mul]
  have hrest : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), w i * d i = γ * d ψ := by
    rw [Finset.sum_eq_single ψ (fun i hi hiψ => by rw [hwv i hi, ite_eq_right hiψ, zero_mul])
      (fun h => absurd hψ h), hwv ψ hψ, ite_eq_left rfl]
  rw [hvw, hsplit, hodd, hq, hrest, v0, v1, v2, v3, v4]
  simp only [caseZ0, caseZ2, caseW, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

end Generic

end Frame

end CFSG.Wreathed.FlatComplete
