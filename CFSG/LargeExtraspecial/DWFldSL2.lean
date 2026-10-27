module

public import CFSG.LargeExtraspecial.DW2AOutInput

public section

namespace CFSG.LargeExtraspecial.DW

open Matrix

section TransClass

variable {X : Type} [Group X] {D : Set X}

theorem IsTransClass34.conj_mem (hD : IsTransClass34 D) (g : X) {d : X} (hd : d ∈ D) :
    g * d * g⁻¹ ∈ D := by
  obtain ⟨d₀, -, hd₀⟩ := hD.2.1
  exact (hd₀ _).2 (((hd₀ d).1 hd).trans (isConj_iff.2 ⟨g, rfl⟩))

theorem IsTransClass34.exists_pow_eq_one [Finite X] (hD : IsTransClass34 D) {d e : X}
    (hd : d ∈ D) (he : e ∈ D) : ∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧ (d * e) ^ k = 1 :=
  ⟨orderOf (d * e), orderOf_pos (d * e), hD.2.2.2.1 d hd e he, pow_orderOf_eq_one _⟩

end TransClass

section TwoByTwo

variable {K : Type*} [Field K] [CharP K 2]

theorem sq_eq_trace_smul_add_one {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    A ^ 2 = A.trace • A + 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [det_fin_two] at hA
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, trace_fin_two, one_apply]
  · linear_combination (-1 : K) * hA - h2
  · ring
  · ring
  · linear_combination (-1 : K) * hA - h2

theorem trace_smul_one (c : K) : (c • (1 : Matrix (Fin 2) (Fin 2) K)).trace = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [trace_smul, trace_one, Fintype.card_fin]
  simp [h2]

theorem pow_ne_smul_one {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) (h0 : A.trace ≠ 0)
    (h1 : A.trace ≠ 1) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (c : K) :
    A ^ k ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : A * A = A.trace • A + 1 := by rw [← sq]; exact sq_eq_trace_smul_add_one hA
  set τ := A.trace with hτ
  obtain ⟨α, β, hα, hk⟩ : ∃ α β : K, α ≠ 0 ∧
      A ^ k = α • A + β • (1 : Matrix (Fin 2) (Fin 2) K) := by
    interval_cases k
    · exact ⟨1, 0, one_ne_zero, by simp⟩
    · exact ⟨τ, 1, h0, by rw [sq, hsq, one_smul]⟩
    · refine ⟨τ ^ 2 + 1, τ, ?_, ?_⟩
      · intro h
        apply h1
        have h' : (τ + 1) ^ 2 = 0 := by linear_combination h + τ * h2
        linear_combination (pow_eq_zero_iff (n := 2) (by norm_num)).1 h' - h2
      · rw [pow_succ, sq, hsq, add_mul, smul_mul_assoc, one_mul, hsq]
        module
    · refine ⟨τ ^ 3, τ ^ 2 + 1, pow_ne_zero 3 h0, ?_⟩
      rw [show A ^ 4 = (A * A) * (A * A) by rw [← sq, ← sq, ← pow_mul]]
      rw [hsq]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      rw [hsq]
      match_scalars <;> first | ring1 | linear_combination τ * h2
  intro hc
  rw [hc] at hk
  have hA' : A = (α⁻¹ * (c - β)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have : α • A = (c - β) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [sub_smul, hk]; abel
    rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hα, one_smul]
  exact h0 (by rw [hτ, hA', trace_smul_one])

end TwoByTwo

section Plane

variable {K : Type*} [Field K] [CharP K 2] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP K 2] in
theorem pow_mulVec_pair {M : Matrix ι ι K} {w u : ι → K} {A : Matrix (Fin 2) (Fin 2) K}
    (hw : M *ᵥ w = A 0 0 • w + A 1 0 • u) (hu : M *ᵥ u = A 0 1 • w + A 1 1 • u) (k : ℕ) :
    (M ^ k) *ᵥ w = (A ^ k) 0 0 • w + (A ^ k) 1 0 • u ∧
      (M ^ k) *ᵥ u = (A ^ k) 0 1 • w + (A ^ k) 1 1 • u := by
  induction k with
  | zero => simp [one_apply]
  | succ k ih =>
    rw [pow_succ, pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, hw, hu]
    simp only [mulVec_add, mulVec_smul, ih.1, ih.2, mul_apply, Fin.sum_univ_two]
    constructor <;> module

theorem pow_ne_smul_one_of_plane {M : Matrix ι ι K} {w u : ι → K}
    (hind : ∀ a b : K, a • w + b • u = 0 → a = 0 ∧ b = 0) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A.det = 1) (h0 : A.trace ≠ 0) (h1 : A.trace ≠ 1)
    (hw : M *ᵥ w = A 0 0 • w + A 1 0 • u) (hu : M *ᵥ u = A 0 1 • w + A 1 1 • u)
    {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (c : K) : M ^ k ≠ c • (1 : Matrix ι ι K) := by
  intro hc
  obtain ⟨hkw, hku⟩ := pow_mulVec_pair hw hu k
  rw [hc, smul_mulVec, one_mulVec] at hkw hku
  obtain ⟨e00, e10⟩ := hind ((A ^ k) 0 0 - c) ((A ^ k) 1 0) (by
    rw [sub_smul, sub_add_eq_add_sub, ← hkw, sub_self])
  obtain ⟨e01, e11⟩ := hind ((A ^ k) 0 1) ((A ^ k) 1 1 - c) (by
    rw [sub_smul, ← add_sub_assoc, ← hku, sub_self])
  apply pow_ne_smul_one hA h0 h1 hk1 hk4 c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply]
  · linear_combination e00
  · linear_combination e01
  · linear_combination e10
  · linear_combination e11

omit [Fintype ι] [DecidableEq ι] in
theorem neg_pi_eq_self (y : ι → K) : -y = y := by
  funext i
  exact CharTwo.neg_eq (y i)

theorem mulVec_conj_plane {B H H' : Matrix ι ι K} (hH : H' * H = 1) {w u : ι → K} {x : K}
    (hBw : B *ᵥ w = w) (hBu : B *ᵥ u = u + w) (hHw : H *ᵥ w = w + x • u) (hHu : H *ᵥ u = u) :
    (B * H * B * H') *ᵥ w = (1 + x + x ^ 2) • w + x ^ 2 • u ∧
      (B * H * B * H') *ᵥ u = x • w + (1 + x) • u := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hH'u : H' *ᵥ u = u := by
    conv_lhs => rw [← hHu]
    rw [mulVec_mulVec, hH, one_mulVec]
  have hH'w : H' *ᵥ w = w + x • u := by
    have : H *ᵥ (w + x • u) = w := by
      rw [mulVec_add, mulVec_smul, hHw, hHu, add_assoc, ← add_smul, ← two_mul, h2, zero_mul,
        zero_smul, add_zero]
    conv_lhs => rw [← this]
    rw [mulVec_mulVec, hH, one_mulVec]
  constructor
  · rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hH'w]
    simp only [mulVec_add, mulVec_smul, hBw, hBu, hHw, hHu]
    match_scalars <;> first | ring1 | linear_combination x * h2
  · rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hH'u]
    simp only [mulVec_add, mulVec_smul, hBw, hBu, hHw, hHu]
    match_scalars <;> first | ring1 | linear_combination h2

theorem conj_pow_ne_smul_one {B H H' : Matrix ι ι K} (hH : H' * H = 1) {w u : ι → K}
    (hind : ∀ a b : K, a • w + b • u = 0 → a = 0 ∧ b = 0) {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hBw : B *ᵥ w = w) (hBu : B *ᵥ u = u + w) (hHw : H *ᵥ w = w + x • u) (hHu : H *ᵥ u = u)
    {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (c : K) :
    (B * H * B * H') ^ k ≠ c • (1 : Matrix ι ι K) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨hw, hu⟩ := mulVec_conj_plane hH hBw hBu hHw hHu
  set A : Matrix (Fin 2) (Fin 2) K := !![1 + x + x ^ 2, x; x ^ 2, 1 + x] with hAdef
  have hA : A.det = 1 := by
    rw [hAdef, det_fin_two_of]
    linear_combination (1 + x) * x * h2
  have htr : A.trace = x ^ 2 := by
    rw [hAdef, trace_fin_two_of]
    linear_combination (1 + x) * h2
  refine pow_ne_smul_one_of_plane (A := A) hind hA ?_ ?_ ?_ ?_ hk1 hk4 c
  · rw [htr]
    exact pow_ne_zero 2 hx0
  · rw [htr]
    intro h
    apply hx1
    have h' : (x + 1) ^ 2 = 0 := by linear_combination h + (x + 1) * h2
    linear_combination (pow_eq_zero_iff (n := 2) (by norm_num)).1 h' - h2
  · simpa [hAdef] using hw
  · simpa [hAdef] using hu

theorem exists_pair_of_involution {B : Matrix ι ι K} (hB2 : B * B = 1) (hB1 : B ≠ 1) :
    ∃ w v : ι → K, w ≠ 0 ∧ B *ᵥ w = w ∧ B *ᵥ v = v + w := by
  obtain ⟨v, hv⟩ : ∃ v : ι → K, B *ᵥ v ≠ v := by
    by_contra! h
    apply hB1
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    simpa [one_apply, Pi.single_apply, eq_comm] using this
  refine ⟨B *ᵥ v - v, v, sub_ne_zero.2 hv, ?_, by abel⟩
  rw [mulVec_sub, mulVec_mulVec, hB2, one_mulVec, ← neg_sub, neg_pi_eq_self]

omit [CharP K 2] [DecidableEq ι] in
theorem independent_of_pair {B : Matrix ι ι K} {w u : ι → K} (hw0 : w ≠ 0) (hBw : B *ᵥ w = w)
    (hBu : B *ᵥ u = u + w) : ∀ a b : K, a • w + b • u = 0 → a = 0 ∧ b = 0 := by
  intro c d hcd
  have h' : B *ᵥ (c • w + d • u) = 0 := by rw [hcd, mulVec_zero]
  rw [mulVec_add, mulVec_smul, mulVec_smul, hBw, hBu, smul_add, ← add_assoc, hcd,
    zero_add] at h'
  have hd : d = 0 := (smul_eq_zero.1 h').resolve_right hw0
  subst hd
  rw [zero_smul, add_zero] at hcd
  exact ⟨(smul_eq_zero.1 hcd).resolve_right hw0, rfl⟩

theorem exists_plane_transvection {B : Matrix ι ι K} (hB2 : B * B = 1) (hB1 : B ≠ 1) (x : K) :
    ∃ (w u : ι → K) (H : Matrix ι ι K), (∀ a b : K, a • w + b • u = 0 → a = 0 ∧ b = 0) ∧
      B *ᵥ w = w ∧ B *ᵥ u = u + w ∧ H *ᵥ w = w + x • u ∧ H *ᵥ u = u ∧ H.det = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨w, v, hw0, hBw, hBv⟩ := exists_pair_of_involution hB2 hB1
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw0
  set a : ι → K := Pi.single i (w i)⁻¹ with hadef
  have haw : a ⬝ᵥ w = 1 := by
    rw [hadef, single_dotProduct, inv_mul_cancel₀ hi]
  set u := v + (a ⬝ᵥ v) • w with hudef
  have hau : a ⬝ᵥ u = 0 := by
    rw [hudef, dotProduct_add, dotProduct_smul, haw, smul_eq_mul, mul_one, ← two_mul, h2,
      zero_mul]
  have hBu : B *ᵥ u = u + w := by
    rw [hudef, mulVec_add, mulVec_smul, hBv, hBw]
    abel
  set H : Matrix ι ι K := 1 + vecMulVec u (x • a) with hHdef
  have hH : ∀ y, H *ᵥ y = y + (x * (a ⬝ᵥ y)) • u := by
    intro y
    rw [hHdef, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_dotProduct,
      smul_eq_mul]
  refine ⟨w, u, H, independent_of_pair hw0 hBw hBu, hBw, hBu, ?_, ?_, ?_⟩
  · rw [hH, haw, mul_one]
  · rw [hH, hau, mul_zero, zero_smul, add_zero]
  · rw [hHdef, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, smul_dotProduct,
      hau, smul_zero, add_zero]

end Plane

section SL2

variable {X : Type} [Group X] {D : Set X}

theorem exists_conj_pow_ne_one_sl2 {F : Type*} [Field F] [CharP F 2] {s : F} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ k : ℕ, 1 ≤ k → k ≤ 4 → (g * (h * g * h⁻¹)) ^ k ≠ 1 := by
  have hB2 : (g : Matrix (Fin 2) (Fin 2) F) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hg2, Matrix.SpecialLinearGroup.coe_one]
  have hB1 : (g : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h =>
    hg1 (Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm))
  obtain ⟨w, u, H, hind, hBw, hBu, hHw, hHu, hdet⟩ := exists_plane_transvection hB2 hB1 s
  let h : Matrix.SpecialLinearGroup (Fin 2) F := ⟨H, hdet⟩
  have hcoe : (h : Matrix (Fin 2) (Fin 2) F) = H := rfl
  refine ⟨h, fun k hk1 hk4 hk => ?_⟩
  have hH : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * H = 1 := by
    rw [← hcoe, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  apply conj_pow_ne_smul_one hH hind hs0 hs1 hBw hBu hHw hHu hk1 hk4 1
  rw [one_smul, ← hcoe, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_pow,
    ← Matrix.SpecialLinearGroup.coe_one]
  congr 1
  rw [← hk]
  simp only [mul_assoc]
  rfl

theorem not_isTransClass34_of_sl2 [Finite X] (hD : IsTransClass34 D) {F : Type*} [Field F]
    [CharP F 2] {s : F} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (φ : Matrix.SpecialLinearGroup (Fin 2) F →* X) (hφ : Function.Injective φ)
    {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg : φ g ∈ D) : False := by
  obtain ⟨hne, hsq⟩ := hD.2.2.1 _ hg
  have hg2 : g * g = 1 := hφ (by rw [map_mul, hsq, map_one])
  have hg1 : g ≠ 1 := fun h => hne (by rw [h, map_one])
  obtain ⟨h, hh⟩ := exists_conj_pow_ne_one_sl2 hs0 hs1 hg2 hg1
  have he : φ (h * g * h⁻¹) ∈ D := by
    rw [map_mul, map_mul, map_inv]
    exact hD.conj_mem _ hg
  obtain ⟨k, hk1, hk4, hk⟩ := hD.exists_pow_eq_one hg he
  exact hh k hk1 hk4 (hφ (by rw [map_pow, map_mul, hk, map_one]))

end SL2

end CFSG.LargeExtraspecial.DW
