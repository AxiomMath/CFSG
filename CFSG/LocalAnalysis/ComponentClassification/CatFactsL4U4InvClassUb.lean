module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace InvClassU

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

variable {p f : ℕ} {K : Type} [Field K]

theorem mul_eq_one_comm_of_card {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (hc : Fintype.card n = Fintype.card m) {E : Matrix m n K}
    {F : Matrix n m K} (hFE : F * E = 1) : E * F = 1 := by
  let e : n ≃ m := Fintype.equivOfCardEq hc
  have h1 : F.submatrix e.symm id * E.submatrix id e.symm = 1 := by
    rw [← submatrix_mul F E e.symm id e.symm Function.bijective_id, hFE, submatrix_one_equiv]
  have h2 := mul_eq_one_comm.mp h1
  rwa [submatrix_mul_equiv, submatrix_id_id] at h2

theorem det_eq_of_mul_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (hc : Fintype.card n = Fintype.card m) {A : Matrix m m K} {E : Matrix m n K}
    {F : Matrix n m K} (hFE : F * E = 1) {D : Matrix n n K} (hAE : A * E = E * D) :
    A.det = D.det := by
  let e : n ≃ m := Fintype.equivOfCardEq hc
  have hFE' : F.submatrix e.symm id * E.submatrix id e.symm = 1 := by
    rw [← submatrix_mul F E e.symm id e.symm Function.bijective_id, hFE, submatrix_one_equiv]
  have hAE' : A * E.submatrix id e.symm = E.submatrix id e.symm * D.submatrix e.symm e.symm := by
    have h1 : (A * E).submatrix id e.symm = A * E.submatrix id e.symm := by
      rw [submatrix_mul A E id id e.symm Function.bijective_id, submatrix_id_id]
    rw [← h1, hAE, submatrix_mul E D id e.symm e.symm e.symm.bijective]
  have hdet := congrArg Matrix.det hAE'
  rw [det_mul, det_mul, det_submatrix_equiv_self] at hdet
  have hE0 : (E.submatrix id e.symm).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hFE'
    rw [det_mul, h0, mul_zero, det_one] at this
    exact zero_ne_one this
  exact mul_right_cancel₀ hE0 (by rw [hdet, mul_comm])

theorem colMat_mul_diagonal {ι κ : Type*} [Fintype κ] [DecidableEq κ] (v : κ → ι → K)
    (d : κ → K) : colMat v * diagonal d = colMat fun i => d i • v i := by
  ext a i
  simp [colMat, mul_diagonal, mul_comm]

theorem mul_colMat_of_eigen {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι K} {v : κ → ι → K} {d : κ → K} (hv : ∀ i, A *ᵥ v i = d i • v i) :
    A * colMat v = colMat v * diagonal d := by
  rw [mul_colMat, colMat_mul_diagonal]
  congr 1
  funext i
  exact hv i

theorem card_hypIndex_two_zero : Fintype.card (HypIndex 2 0) = 4 := by
  simp [HypIndex]

theorem det_of_eigen (h : UnitaryFieldData p f K) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hκ : Fintype.card κ = 4) {v : κ → HypIndex 2 0 → K} {G Gi : Matrix κ κ K}
    (hG : (Matrix.of fun i j => hypForm h 2 0 (v i) (v j)) = G) (hGi : Gi * G = 1)
    {A : Matrix (HypIndex 2 0) (HypIndex 2 0) K} {d : κ → K}
    (hv : ∀ i, A *ᵥ v i = d i • v i) : A.det = ∏ i, d i := by
  have hFE : (Gi * ((colMat v).map h.bar)ᵀ * hypGram 2 0 K) * colMat v = 1 := by
    have hgram := gram_colMat_eq_hypForm h v
    simp only [Matrix.mul_assoc] at hgram ⊢
    rw [hgram, hG, hGi]
  rw [det_eq_of_mul_eq (by rw [hκ, card_hypIndex_two_zero]) hFE (mul_colMat_of_eigen hv),
    det_diagonal]

theorem inner_det (h : UnitaryFieldData p f K) {A : GL (HypIndex 2 0) K} {σ : K ≃+* K}
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hA : A ∈ hypUnitary h 2 0) {y : hypPSU h 2 0}
    (hy : semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ = MulAut.conj y) :
    σ = RingEquiv.refl K ∧ ∃ c : K, h.norm c = 1 ∧
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = c ^ 4 := by
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 0 y
  set x₁ : semilinearSimilitudes h 2 0 := ⟨_, inl_mem_semilinearSimilitudes g⟩ with hx₁
  have hconj : semilinearAutHom h (by norm_num) (by norm_num) x₁ =
      MulAut.conj (hypProj h 2 0 g) := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨g', rfl⟩ := hypProj_surjective h 2 0 z
    rw [semilinearAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have h1 : semilinearAutHom h (by norm_num) (by norm_num) (x₁⁻¹ * ⟨_, hx⟩) = 1 := by
    rw [map_mul, map_inv, hconj, hy, inv_mul_cancel]
  obtain ⟨hright, c, hc⟩ :=
    (semilinearAutHom_eq_one_iff h (by norm_num) (by norm_num) (by norm_num) _).mp h1
  simp [hx₁] at hright hc
  have hgU : (g : GL (HypIndex 2 0) K) ∈ hypUnitary h 2 0 := (mem_hypSU.mp g.2).1
  have hA' : A = g * GeneralLinearGroup.scalar (HypIndex 2 0) c := by
    rw [← hc, mul_inv_cancel_left]
  have hmem : GeneralLinearGroup.scalar (HypIndex 2 0) c ∈ hypUnitary h 2 0 :=
    hc ▸ mul_mem (inv_mem hgU) hA
  refine ⟨hright, c, norm_eq_one_of_smul h (by norm_num) hmem (by
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]), ?_⟩
  rw [hA', Units.val_mul, det_mul, (mem_hypSU.mp g.2).2, one_mul,
    GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, card_hypIndex_two_zero]

theorem false_of_pow_four_eq_neg_one (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hq : p ^ f % 4 = 1) {z : K} (hz : z ^ 4 = -1) (hN : h.norm z = 1) : False := by
  rw [h.norm_eq_pow] at hN
  obtain ⟨j, hj⟩ : ∃ j, p ^ f + 1 = 4 * j + 2 := ⟨p ^ f / 4, by omega⟩
  rw [hj, pow_add, pow_mul, hz] at hN
  have h4 : z ^ 4 = 1 := by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring]
    rcases neg_one_pow_eq_or K j with h1 | h1
    · rw [h1, one_mul] at hN
      rw [hN, one_pow]
    · rw [h1, neg_one_mul, neg_eq_iff_eq_neg] at hN
      rw [hN]
      ring
  exact two_ne_zero_of_odd h hp (by linear_combination hz - h4)

theorem false_of_pow_four_eq_one (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hq : p ^ f % 4 = 3) {z : K} (hz : z ^ 4 = 1) (hN : h.norm z = -1) : False := by
  rw [h.norm_eq_pow] at hN
  obtain ⟨j, hj⟩ : ∃ j, p ^ f + 1 = 4 * j := ⟨(p ^ f + 1) / 4, by omega⟩
  rw [hj, pow_mul, hz, one_pow] at hN
  exact two_ne_zero_of_odd h hp (by linear_combination hN)

section Outer

variable (h : UnitaryFieldData p f K) {A : GL (HypIndex 2 0) K} {σ : K ≃+* K}
  (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
  (hA : A ∈ hypUnitary h 2 0)

include hx hA

theorem not_inner_bar (hσ : ∀ c, σ c = h.bar c) (y : hypPSU h 2 0) :
    semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ ≠ MulAut.conj y := by
  intro hy
  obtain ⟨hσ1, -⟩ := inner_det h hx hA hy
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  apply hc
  rw [← hσ, hσ1]
  rfl

theorem not_inner_D1 (hp : p ≠ 2) (hq : p ^ f % 4 = 1) {d : K} (hd : h.norm d = 1)
    {v : Fin 3 ⊕ Fin 1 → HypIndex 2 0 → K}
    (hv : ∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0)
    (hAv : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
      Sum.elim (fun _ => d) (fun _ => -d) i • v i) (y : hypPSU h 2 0) :
    semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ ≠ MulAut.conj y := by
  intro hy
  obtain ⟨-, c, hc, hdet⟩ := inner_det h hx hA hy
  have hdA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = -d ^ 4 := by
    rw [det_of_eigen h (by simp) (G := 1) (Gi := 1) (by ext i j; simp [hv, one_apply])
      (Matrix.one_mul 1) hAv]
    simp [Fintype.prod_sum_type]
    ring
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp [UnitaryFieldData.norm] at hd
  refine false_of_pow_four_eq_neg_one h hp hq (z := c / d) ?_ ?_
  · rw [div_pow, ← hdet, hdA]
    field_simp
  · rw [div_eq_mul_inv, norm_mul_eq h, norm_inv_eq h, hc, hd, inv_one, mul_one]

theorem not_inner_pair (hp : p ≠ 2) (hq : p ^ f % 4 = 3) {l : K} (hl : h.norm l = -1)
    {e g : Fin 2 → HypIndex 2 0 → K}
    (hAe : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e i = l • e i)
    (hAg : ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g i = (-l) • g i)
    (hee : ∀ i j, hypForm h 2 0 (e i) (e j) = 0) (hgg : ∀ i j, hypForm h 2 0 (g i) (g j) = 0)
    (heg : ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0) (y : hypPSU h 2 0) :
    semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩ ≠ MulAut.conj y := by
  intro hy
  obtain ⟨-, c, hc, hdet⟩ := inner_det h hx hA hy
  have hge : ∀ i j, hypForm h 2 0 (g i) (e j) = if i = j then 1 else 0 := fun i j => by
    rw [← (hypForm_isSymm h).eq (e j) (g i), heg]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  have hG : (Matrix.of fun i j => hypForm h 2 0 (Sum.elim e g i) (Sum.elim e g j)) =
      (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    ext (i | i) (j | j) <;> simp [hee, hgg, heg, hge, one_apply]
  have hGG : (fromBlocks 0 1 1 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      fromBlocks 0 1 1 0 = 1 := by
    rw [fromBlocks_multiply]
    simp [fromBlocks_one]
  have hdA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).det = l ^ 4 := by
    rw [det_of_eigen h (by simp) hG hGG (d := Sum.elim (fun _ => l) (fun _ => -l))
      (by rintro (i | i); exacts [hAe i, hAg i])]
    simp [Fintype.prod_sum_type]
    ring
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp [UnitaryFieldData.norm] at hc
  refine false_of_pow_four_eq_one h hp hq (z := l / c) ?_ ?_
  · rw [div_pow, ← hdA, hdet]
    exact div_self (pow_ne_zero 4 hc0)
  · rw [div_eq_mul_inv, norm_mul_eq h, norm_inv_eq h, hc, hl, inv_one, mul_one]

end Outer

end InvClassU

end CFSG.ComponentClassification.CatFactsL4U4
