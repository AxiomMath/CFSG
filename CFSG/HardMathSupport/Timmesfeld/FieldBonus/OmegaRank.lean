module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

open Classical in
@[expose] noncomputable def eFr (f : Fin 4 → ι) (hf : Function.Injective f) :
    ι ≃ Fin 4 ⊕ ↥(Set.range f)ᶜ :=
  (Equiv.Set.sumCompl (Set.range f)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective f hf).symm (Equiv.refl _))

theorem eFr_apply_f (f : Fin 4 → ι) (hf : Function.Injective f) (k : Fin 4) :
    eFr f hf (f k) = Sum.inl k := by
  classical
  simp [eFr, Equiv.Set.sumCompl_symm_apply_of_mem]

theorem eFr_apply_of_not (f : Fin 4 → ι) (hf : Function.Injective f) {a : ι}
    (ha : a ∉ Set.range f) : ∃ h : a ∈ (Set.range f)ᶜ, eFr f hf a = Sum.inr ⟨a, h⟩ := by
  classical
  refine ⟨ha, ?_⟩
  simp [eFr, Equiv.Set.sumCompl_symm_apply_of_notMem, ha]

theorem eFr_symm_inl (f : Fin 4 → ι) (hf : Function.Injective f) (k : Fin 4) :
    (eFr f hf).symm (Sum.inl k) = f k := by
  rw [Equiv.symm_apply_eq, eFr_apply_f]

@[expose] noncomputable def blk4 (f : Fin 4 → ι) (hf : Function.Injective f)
    (N : Matrix (Fin 4) (Fin 4) K) :
    Matrix ι ι K :=
  (fromBlocks N 0 0 1 : Matrix (Fin 4 ⊕ ↥(Set.range f)ᶜ) (Fin 4 ⊕ ↥(Set.range f)ᶜ) K).submatrix
    (eFr f hf) (eFr f hf)

theorem blk4_mul (f : Fin 4 → ι) (hf : Function.Injective f) (N N' : Matrix (Fin 4) (Fin 4) K) :
    blk4 f hf N * blk4 f hf N' = blk4 f hf (N * N') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]

theorem blk4_one (f : Fin 4 → ι) (hf : Function.Injective f) :
    blk4 f hf (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  unfold blk4
  rw [fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blk4_mulVec_f (f : Fin 4 → ι) (hf : Function.Injective f) (N : Matrix (Fin 4) (Fin 4) K)
    (v : ι → K) (k : Fin 4) : (blk4 f hf N *ᵥ v) (f k) = ∑ l, N k l * v (f l) := by
  unfold blk4 Matrix.mulVec dotProduct
  rw [← (eFr f hf).symm.sum_comp, Fintype.sum_sum_type]
  simp [eFr_apply_f, eFr_symm_inl]

theorem blk4_mulVec_of_not (f : Fin 4 → ι) (hf : Function.Injective f)
    (N : Matrix (Fin 4) (Fin 4) K) (v : ι → K) {a : ι} (ha : a ∉ Set.range f) :
    (blk4 f hf N *ᵥ v) a = v a := by
  obtain ⟨h, hea⟩ := eFr_apply_of_not f hf ha
  unfold blk4 Matrix.mulVec dotProduct
  rw [← (eFr f hf).symm.sum_comp, Fintype.sum_sum_type]
  have h1 : (eFr f hf).symm (Sum.inr ⟨a, h⟩) = a := by
    rw [Equiv.symm_apply_eq]; exact hea.symm
  simp [hea, Matrix.one_apply, h1]

@[expose] def lmat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![A 0 0, 0, 0, -A 0 1; 0, A 0 0, A 0 1, 0; 0, A 1 0, A 1 1, 0; -A 1 0, 0, 0, A 1 1]

@[expose] def rmat (B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![B 1 1, -B 1 0, 0, 0; -B 0 1, B 0 0, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

theorem lmat_mul (A B : Matrix (Fin 2) (Fin 2) K) : lmat (A * B) = lmat A * lmat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lmat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

theorem rmat_mul (A B : Matrix (Fin 2) (Fin 2) K) : rmat (A * B) = rmat A * rmat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rmat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two] <;> ring

theorem lmat_one : lmat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lmat]

theorem rmat_one : rmat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rmat]

@[expose] def q4 (u : Fin 4 → K) : K := u 0 * u 2 + u 1 * u 3

theorem q4_lmat (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) (u : Fin 4 → K) :
    q4 (lmat A *ᵥ u) = q4 u := by
  rw [Matrix.det_fin_two] at hA
  simp only [q4, lmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  simp
  linear_combination (u 0 * u 2 + u 1 * u 3) * hA

theorem q4_rmat (B : Matrix (Fin 2) (Fin 2) K) (hB : B.det = 1) (u : Fin 4 → K) :
    q4 (rmat B *ᵥ u) = q4 u := by
  rw [Matrix.det_fin_two] at hB
  simp only [q4, rmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  simp
  linear_combination (u 0 * u 2 + u 1 * u 3) * hB

theorem lmat_rmat_comm (A B : Matrix (Fin 2) (Fin 2) K) :
    lmat A * rmat B = rmat B * lmat A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lmat, rmat, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem blk4_apply_f (f : Fin 4 → ι) (hf : Function.Injective f) (N : Matrix (Fin 4) (Fin 4) K)
    (k l : Fin 4) : blk4 f hf N (f k) (f l) = N k l := by
  unfold blk4
  simp [eFr_apply_f]

@[expose] noncomputable def gen (f : Fin 4 → ι) (hf : Function.Injective f)
    (m : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 4) (Fin 4) K) (h1 : m 1 = 1)
    (hm : ∀ A B, m (A * B) = m A * m B) : SL(2, K) →* GL ι K :=
  MonoidHom.toHomUnits
    { toFun := fun A => blk4 f hf (m (A : Matrix (Fin 2) (Fin 2) K))
      map_one' := by simp [h1, blk4_one]
      map_mul' := fun A B => by
        rw [Matrix.SpecialLinearGroup.coe_mul, hm, ← blk4_mul] }

theorem coe_gen (f : Fin 4 → ι) (hf : Function.Injective f)
    (m : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 4) (Fin 4) K) (h1 : m 1 = 1)
    (hm : ∀ A B, m (A * B) = m A * m B) (A : SL(2, K)) :
    ((gen f hf m h1 hm A : GL ι K) : Matrix ι ι K) = blk4 f hf (m (A : Matrix (Fin 2) (Fin 2) K)) :=
  rfl

section Omega

variable (Q : (ι → K) → K) (f : Fin 4 → ι) (hf : Function.Injective f)
  (HQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range f → v a = w a) →
    Q v - Q w = q4 (v ∘ f) - q4 (w ∘ f))

include HQ in
theorem Q_blk4 (N : Matrix (Fin 4) (Fin 4) K) (hN : ∀ u, q4 (N *ᵥ u) = q4 u) (v : ι → K) :
    Q (blk4 f hf N *ᵥ v) = Q v := by
  have h := HQ (blk4 f hf N *ᵥ v) v (fun a ha => blk4_mulVec_of_not f hf N v ha)
  have h2 : (blk4 f hf N *ᵥ v) ∘ f = N *ᵥ (v ∘ f) := by
    funext k
    rw [Function.comp_apply, blk4_mulVec_f]
    rfl
  rw [h2, hN] at h
  linear_combination h

include HQ in
theorem gen_mem_omega (m : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 4) (Fin 4) K) (h1 : m 1 = 1)
    (hm : ∀ A B, m (A * B) = m A * m B)
    (hq : ∀ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 → ∀ u, q4 (m A *ᵥ u) = q4 u)
    {a : K} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) (A : SL(2, K)) :
    gen f hf m h1 hm A ∈ StatedOmega Q := by
  have hperf : ⁅(⊤ : Subgroup SL(2, K)), ⊤⁆ = ⊤ := Matrix.SL2.commutator_eq_top ha hasq
  have hle : (⊤ : Subgroup SL(2, K)).map (gen f hf m h1 hm) ≤
      Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} := by
    rintro _ ⟨B, -, rfl⟩
    refine Subgroup.subset_closure ?_
    intro v
    rw [coe_gen]
    exact Q_blk4 Q f hf HQ _ (hq _ B.2) v
  have hA : A ∈ ⁅(⊤ : Subgroup SL(2, K)), (⊤ : Subgroup SL(2, K))⁆ := by rw [hperf]; trivial
  have := Subgroup.mem_map_of_mem (gen f hf m h1 hm) hA
  rw [Subgroup.map_commutator] at this
  exact Subgroup.commutator_mono hle hle this

end Omega

@[expose] def c3 : SL(2, K) := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem c3_pow_three : (c3 : SL(2, K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c3, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_c3_sq : (((c3 : SL(2, K)) ^ 2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
    !![-1, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c3, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

section Rank

variable [Finite K] (Q : (ι → K) → K) (f : Fin 4 → ι) (hf : Function.Injective f)
  (HQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range f → v a = w a) →
    Q v - Q w = q4 (v ∘ f) - q4 (w ∘ f))

include hf HQ in
theorem two_le_pRank_omega {a : K} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x : GL ι K := gen f hf lmat lmat_one lmat_mul c3 with hxdef
  set y : GL ι K := gen f hf rmat rmat_one rmat_mul c3 with hydef
  have hxO : x ∈ StatedOmega Q :=
    gen_mem_omega Q f hf HQ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) ha hasq c3
  have hyO : y ∈ StatedOmega Q :=
    gen_mem_omega Q f hf HQ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) ha hasq c3
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← map_pow, c3_pow_three, map_one]
  have hy3 : y ^ 3 = 1 := by rw [hydef, ← map_pow, c3_pow_three, map_one]
  have hcomm : x * y = (1 : GL ι K) * (y * x) := by
    rw [one_mul]
    ext1
    simp only [Units.val_mul, hxdef, hydef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hx1 : x ∉ StatedScalars ι K := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (f 0) (f 3)) hu
    simp only [GeneralLinearGroup.coe_scalar, hxdef, coe_gen, blk4_apply_f, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ (hf.ne (by decide : (0 : Fin 4) ≠ 3))] at h1
    simp [lmat, c3] at h1
  have hy1 : ∀ n : ℕ, ∀ s ∈ StatedScalars ι K, x ^ n * s ≠ y := by
    rintro n _ ⟨u, rfl⟩ hmc
    have key : ∀ k l, lmat (((c3 : SL(2, K)) ^ n : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l *
        (u : K) = rmat ((c3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l := by
      intro k l
      have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (f k) (f l)) hmc
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, ← map_pow, coe_gen,
        Matrix.scalar_apply, Matrix.mul_diagonal, blk4_apply_f] at h1
      exact h1
    have hn : (c3 : SL(2, K)) ^ n = c3 ^ (n % 3) := by
      conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, c3_pow_three, one_pow, mul_one]
    rw [hn] at key
    have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : n % 3
    · have e := key 0 1
      simp [lmat, rmat, c3] at e
    · have e := key 0 0
      rw [pow_one] at e
      simp [lmat, rmat, c3] at e
    · have e := key 0 1
      rw [coe_c3_sq] at e
      simp [lmat, rmat, c3] at e
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_statedProj
    (H := StatedOmega Q) (p := 3) hxO hyO hx3 hy3 ⟨1, one_mem _, hcomm⟩ hx1 hy1

end Rank

section Forms

variable {m : ℕ}

@[expose] def frame4 (a b : Fin m → ι) (i0 i1 : Fin m) : Fin 4 → ι := ![a i0, a i1, b i0, b i1]

theorem frame4_injective (a b : Fin m → ι) (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) (i0 i1 : Fin m) (h : i0 ≠ i1) :
    Function.Injective (frame4 a b i0 i1) := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;>
    simp [frame4, ha.eq_iff, hb.eq_iff, hab, (hab _ _).symm, h, h.symm] at hkl ⊢

theorem notMem_range_frame4 (a b : Fin m → ι) (ha : Function.Injective a)
    (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j) (i0 i1 i : Fin m) (h0 : i ≠ i0)
    (h1 : i ≠ i1) :
    a i ∉ Set.range (frame4 a b i0 i1) ∧ b i ∉ Set.range (frame4 a b i0 i1) := by
  constructor <;>
  · rintro ⟨k, hk⟩
    fin_cases k <;>
      simp [frame4, ha.eq_iff, hb.eq_iff, hab, (hab _ _).symm, h0, h1, h0.symm, h1.symm] at hk

theorem hq_of_sum (a b : Fin m → ι) (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) (i0 i1 : Fin m) (hne : i0 ≠ i1) (Q R : (ι → K) → K)
    (hR : ∀ v w : ι → K, (∀ x, x ∉ Set.range (frame4 a b i0 i1) → v x = w x) → R v = R w)
    (hQ : ∀ v, Q v = ∑ i, v (a i) * v (b i) + R v) :
    ∀ v w : ι → K, (∀ x, x ∉ Set.range (frame4 a b i0 i1) → v x = w x) →
      Q v - Q w = q4 (v ∘ frame4 a b i0 i1) - q4 (w ∘ frame4 a b i0 i1) := by
  intro v w hvw
  have hs : ∑ i, v (a i) * v (b i) - ∑ i, w (a i) * w (b i) =
      ∑ i ∈ ({i0, i1} : Finset (Fin m)), (v (a i) * v (b i) - w (a i) * w (b i)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_subset (Finset.subset_univ ({i0, i1} : Finset (Fin m))) ?_).symm
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨h1, h2⟩ := notMem_range_frame4 a b ha hb hab i0 i1 i hi.1 hi.2
    rw [hvw _ h1, hvw _ h2, sub_self]
  rw [hQ v, hQ w, hR v w hvw]
  rw [Finset.sum_pair hne] at hs
  have : q4 (v ∘ frame4 a b i0 i1) - q4 (w ∘ frame4 a b i0 i1) =
      (v (a i0) * v (b i0) - w (a i0) * w (b i0)) +
      (v (a i1) * v (b i1) - w (a i1) * w (b i1)) := by
    simp [q4, frame4]; ring
  rw [this, ← hs]
  ring

end Forms

section Instances

variable {K : Type} [Field K] [Finite K]

theorem two_le_pRank_of_pairs {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (a b : Fin m → ι) (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) (i0 i1 : Fin m) (hne : i0 ≠ i1) (Q R : (ι → K) → K)
    (hR : ∀ v w : ι → K, (∀ x, x ∉ Set.range (frame4 a b i0 i1) → v x = w x) → R v = R w)
    (hQ : ∀ v, Q v = ∑ i, v (a i) * v (b i) + R v) {c : K} (hc : c ≠ 0) (hcsq : c ^ 2 ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) :=
  two_le_pRank_omega Q (frame4 a b i0 i1) (frame4_injective a b ha hb hab i0 i1 hne)
    (hq_of_sum a b ha hb hab i0 i1 hne Q R hR hQ) hc hcsq

theorem two_le_pRank_plus {n : ℕ} (hn : 2 ≤ n) {c : K} (hc : c ≠ 0) (hcsq : c ^ 2 ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) :=
  two_le_pRank_of_pairs (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr Sum.inl_injective
    Sum.inr_injective (fun i j => Sum.inl_ne_inr) ⟨0, by omega⟩ ⟨1, by omega⟩
    (by simp [Fin.ext_iff]) _ (fun _ => 0) (fun _ _ _ => rfl)
    (fun v => by simp [StatedQuadPlus]) hc hcsq

theorem two_le_pRank_odd {n : ℕ} (hn : 2 ≤ n) {c : K} (hc : c ≠ 0) (hcsq : c ^ 2 ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K)))) := by
  refine two_le_pRank_of_pairs (Sum.inl : Fin n → Fin n ⊕ Fin n ⊕ Unit)
    (fun i => Sum.inr (Sum.inl i)) Sum.inl_injective
    (fun i j h => by simpa using h) (fun i j => by simp) ⟨0, by omega⟩ ⟨1, by omega⟩
    (by simp [Fin.ext_iff]) _ (fun v => v (Sum.inr (Sum.inr ())) ^ 2) ?_
    (fun v => by simp [StatedQuadOdd]) hc hcsq
  intro v w h
  have : (Sum.inr (Sum.inr ()) : Fin n ⊕ Fin n ⊕ Unit) ∉
      Set.range (frame4 (Sum.inl : Fin n → Fin n ⊕ Fin n ⊕ Unit)
        (fun i => Sum.inr (Sum.inl i)) ⟨0, by omega⟩ ⟨1, by omega⟩) := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [frame4] at hk
  simp only [h _ this]

theorem two_le_pRank_minus {n : ℕ} (hn : 3 ≤ n) (b c' : K) {c : K} (hc : c ≠ 0)
    (hcsq : c ^ 2 ≠ 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c')))) := by
  refine two_le_pRank_of_pairs (Sum.inl : Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (fun i => Sum.inr (Sum.inl i)) Sum.inl_injective
    (fun i j h => by simpa using h) (fun i j => by simp) ⟨0, by omega⟩ ⟨1, by omega⟩
    (by simp [Fin.ext_iff]) _ (fun v => v (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c' * v (Sum.inr (Sum.inr 1)) ^ 2)
    ?_ (fun v => by simp [StatedQuadMinus, add_assoc]) hc hcsq
  intro v w h
  have h0 : (Sum.inr (Sum.inr 0) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) ∉
      Set.range (frame4 (Sum.inl : Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (fun i => Sum.inr (Sum.inl i)) ⟨0, by omega⟩ ⟨1, by omega⟩) := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [frame4] at hk
  have h1 : (Sum.inr (Sum.inr 1) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) ∉
      Set.range (frame4 (Sum.inl : Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (fun i => Sum.inr (Sum.inl i)) ⟨0, by omega⟩ ⟨1, by omega⟩) := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [frame4] at hk
  simp only [h _ h0, h _ h1]

end Instances

theorem char_facts {K : Type} [Field K] {p : ℕ} [CharP K p] (hp : p.Prime) (h2 : p ≠ 2)
    (h3 : p ≠ 3) : (2 : K) ≠ 0 ∧ (2 : K) ^ 2 ≠ 1 := by
  constructor
  · intro h
    have : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  · intro h
    have h' : ((3 : ℕ) : K) = 0 := by
      have : (2 : K) ^ 2 - 1 = 0 := by rw [h]; ring
      push_cast
      linear_combination this
    have : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 h'
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)

theorem two_le_pRank_three_orth {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n p f : ℕ}
    (hC : StatedClassicalModel X t n p f)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
    have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    obtain ⟨c2, c4⟩ := char_facts (K := K) hp h2 h3
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact two_le_pRank_odd (by omega) c2 c4
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hC
    have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    obtain ⟨c2, c4⟩ := char_facts (K := K) hp h2 h3
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact two_le_pRank_plus (by omega) c2 c4
  · obtain ⟨⟨hp, hf, hn⟩, K, _, _, hK, b, c, -, ⟨e⟩⟩ := hC
    have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    obtain ⟨c2, c4⟩ := char_facts (K := K) hp h2 h3
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact two_le_pRank_minus (by omega) b c c2 c4

end CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
