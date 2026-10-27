module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.AGLEmbedding.LinearThreeKit

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K]

theorem sub_one_mulVec_eq_zero {n p : ℕ} (hpK : (p : K) ≠ 0) {U : Matrix (Fin n) (Fin n) K}
    (hU : U ^ p = 1) (y : Fin n → K) (h : U *ᵥ ((U - 1) *ᵥ y) = (U - 1) *ᵥ y) :
    (U - 1) *ᵥ y = 0 := by
  set x := (U - 1) *ᵥ y with hx
  have hpow : ∀ i : ℕ, (U ^ i) *ᵥ x = x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, ih]
  have hN : (∑ i ∈ Finset.range p, U ^ i) * (U - 1) = 0 := by
    rw [geom_sum_mul, hU, sub_self]
  have h1 : (∑ i ∈ Finset.range p, U ^ i) *ᵥ x = (p : K) • x := by
    rw [Matrix.sum_mulVec]
    simp only [hpow, Finset.sum_const, Finset.card_range]
    exact (Nat.cast_smul_eq_nsmul K p x).symm
  have h2 : (∑ i ∈ Finset.range p, U ^ i) *ᵥ x = 0 := by
    rw [hx, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  rw [h2] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hpK

@[expose] def fixedSum {n : ℕ} (p : ℕ) (U : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    Fin n → K :=
  ∑ i ∈ Finset.range p, (U ^ i) *ᵥ y

theorem mulVec_fixedSum {n p : ℕ} {U : Matrix (Fin n) (Fin n) K} (hU : U ^ p = 1)
    (y : Fin n → K) : U *ᵥ fixedSum p U y = fixedSum p U y := by
  rw [fixedSum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_mulVec, ← pow_succ']
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ', hU, pow_zero]

theorem pow_mulVec_sub_mem {n : ℕ} {U : Matrix (Fin n) (Fin n) K} {M : Submodule K (Fin n → K)}
    (hM : ∀ z, U *ᵥ z - z ∈ M) (y : Fin n → K) (i : ℕ) : (U ^ i) *ᵥ y - y ∈ M := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    have h := M.add_mem (hM ((U ^ i) *ᵥ y)) ih
    rwa [sub_add_sub_cancel] at h

theorem pow_mulVec_of_mulVec_eq_smul {n : ℕ} {U : Matrix (Fin n) (Fin n) K} {v : Fin n → K}
    {a : K} (h : U *ᵥ v = a • v) (i : ℕ) : (U ^ i) *ᵥ v = a ^ i • v := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, ← pow_succ]

theorem coe_pow_eq_one {n p : ℕ} {u : SpecialLinearGroup (Fin n) K} (hu : u ^ p = 1) :
    (u : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
  rw [← SpecialLinearGroup.coe_pow, hu, SpecialLinearGroup.coe_one]

theorem mulVec_inv_mulVec {n : ℕ} (g : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
    SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem inv_mulVec_mulVec {n : ℕ} (g : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVec_fixed_of_commute {n : ℕ} {U G : Matrix (Fin n) (Fin n) K} (h : U * G = G * U)
    {v : Fin n → K} (hv : U *ᵥ v = v) : U *ᵥ (G *ᵥ v) = G *ᵥ v := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv]

theorem coe_mul_comm_of_mem_centralizer {n : ℕ} {u g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin n) K))) :
    (u : Matrix (Fin n) (Fin n) K) * g = g * u :=
  congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg u rfl)

theorem mem_centralizer_of_coe_mul_comm {n : ℕ} {u g : SpecialLinearGroup (Fin n) K}
    (h : (u : Matrix (Fin n) (Fin n) K) * g = g * u) :
    g ∈ Subgroup.centralizer ({u} : Set (SpecialLinearGroup (Fin n) K)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  exact Subtype.ext h

theorem forall_fin_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ j, P j := by
  intro j
  fin_cases j
  exacts [h0, h1, h2]

theorem mul_transpose_of_iff {n : ℕ} {b : Fin n → Fin n → K} {A M : Matrix (Fin n) (Fin n) K} :
    A * (Matrix.of b)ᵀ = (Matrix.of b)ᵀ * M ↔ ∀ j, A *ᵥ b j = ∑ i, M i j • b i := by
  constructor
  · intro h j
    ext i
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply] at this
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · intro h
    ext i j
    have := congrFun (h j) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem isUnit_transpose_of {n : ℕ} {b : Fin n → Fin n → K} (hb : LinearIndependent K b) :
    IsUnit (Matrix.of b)ᵀ := by
  rw [Matrix.isUnit_transpose]
  exact Matrix.linearIndependent_rows_iff_isUnit.mp hb

theorem exists_mulVec_eq_sum {n : ℕ} {b : Fin n → Fin n → K} (hb : LinearIndependent K b)
    (M : Matrix (Fin n) (Fin n) K) : ∃ A : Matrix (Fin n) (Fin n) K,
      ∀ j, A *ᵥ b j = ∑ i, M i j • b i := by
  have hP := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose_of hb)
  refine ⟨(Matrix.of b)ᵀ * M * (Matrix.of b)ᵀ⁻¹, mul_transpose_of_iff.mp ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]

theorem det_eq_of_mulVec_eq_sum {n : ℕ} {b : Fin n → Fin n → K} (hb : LinearIndependent K b)
    {A M : Matrix (Fin n) (Fin n) K} (h : ∀ j, A *ᵥ b j = ∑ i, M i j • b i) :
    A.det = M.det := by
  have hP := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose_of hb)
  have h' := congrArg Matrix.det (mul_transpose_of_iff.mpr h)
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h'
  exact mul_left_cancel₀ hP.ne_zero h'

theorem trace_eq_of_mulVec_eq_sum {n : ℕ} {b : Fin n → Fin n → K} (hb : LinearIndependent K b)
    {A M : Matrix (Fin n) (Fin n) K} (h : ∀ j, A *ᵥ b j = ∑ i, M i j • b i) :
    A.trace = M.trace := by
  have hP := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_transpose_of hb)
  have hA : A = (Matrix.of b)ᵀ * M * (Matrix.of b)ᵀ⁻¹ := by
    rw [← mul_transpose_of_iff.mpr h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP,
      Matrix.mul_one]
  rw [hA, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]

theorem eq_of_mulVec_eq {n : ℕ} {b : Fin n → Fin n → K} (hb : LinearIndependent K b)
    {A A' : Matrix (Fin n) (Fin n) K} (h : ∀ j, A *ᵥ b j = A' *ᵥ b j) : A = A' := by
  have h1 : A * (Matrix.of b)ᵀ = A' * (Matrix.of b)ᵀ := by
    ext i j
    have := congrFun (h j) i
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.mulVec,
      dotProduct] using this
  exact (isUnit_transpose_of hb).mul_left_inj.mp h1

theorem exists_sum_smul_eq {n : ℕ} [NeZero n] {b : Fin n → Fin n → K}
    (hb : LinearIndependent K b) (v : Fin n → K) : ∃ c : Fin n → K, ∑ i, c i • b i = v := by
  have hspan := hb.span_eq_top_of_card_eq_finrank (by simp)
  exact (Submodule.mem_span_range_iff_exists_fun K).mp (hspan ▸ Submodule.mem_top)

theorem linearIndependent_pair_of_notMem {V : Type*} [AddCommGroup V] [Module K V]
    {W : Submodule K V} {a b : V} (ha : a ∈ W) (ha0 : a ≠ 0) (hb : b ∉ W) :
    LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    apply hb
    have h2 : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
    have hb' : b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [hb', h2]
    exact W.smul_mem _ (W.neg_mem (W.smul_mem _ ha))
  subst ht
  rw [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.mp hst).resolve_right ha0, rfl⟩

theorem linearIndependent_tail_pair {V : Type*} [AddCommGroup V] [Module K V] {a b c : V}
    (h : LinearIndependent K ![a, b, c]) : LinearIndependent K ![b, c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have := Fintype.linearIndependent_iff.mp h ![0, s, t] (by simp [Fin.sum_univ_three, hst])
  exact ⟨this 1, this 2⟩

theorem mulVec_mulVec_comm {n : ℕ} {U G : Matrix (Fin n) (Fin n) K} (h : U * G = G * U)
    (v : Fin n → K) : G *ᵥ (U *ᵥ v) = U *ᵥ (G *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem flagSpace_one_eq_span {n : ℕ} [NeZero n] :
    flagSpace n K 1 = K ∙ (Pi.single 0 1 : Fin n → K) := by
  have h : {j : Fin n | (j : ℕ) < 1} = {0} := by
    ext j
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff, Nat.lt_one_iff, Fin.ext_iff, Fin.val_zero]
  rw [flagSpace, h, Set.image_singleton]

theorem single_zero_mem_flagSpace_one {n : ℕ} [NeZero n] :
    (Pi.single 0 1 : Fin n → K) ∈ flagSpace n K 1 := by
  rw [flagSpace_one_eq_span]
  exact Submodule.mem_span_singleton_self _

theorem mem_flagSpace_two_iff {v : Fin 3 → K} : v ∈ flagSpace 3 K 2 ↔ v 2 = 0 := by
  rw [mem_flagSpace]
  refine ⟨fun h => h 2 (by simp), fun h j hj => ?_⟩
  fin_cases j <;> simp_all

end CFSG.AGLEmbedding.LinearThreeKit
