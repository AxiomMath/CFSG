module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreA
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.HardMathSupport.Solomon.LocalBalance

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem spIsNilpotent_smul_one_iff [Nonempty ι] {c : K} :
    IsNilpotent (c • (1 : Matrix ι ι K)) ↔ c = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨i⟩ := ‹Nonempty ι›
    have h := congrFun (congrFun hk i) i
    have h2 : (c • (1 : Matrix ι ι K)) ^ k = (c ^ k) • (1 : Matrix ι ι K) := by
      rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow]
    rw [h2] at h
    exact (by simpa using h : c = 0 ∧ ¬ k = 0).1
  · rintro rfl
    exact ⟨1, by simp⟩

theorem spEq_one_of_smul_one_add_nilpotent [Nonempty ι] {z y : Matrix ι ι K} {ζ : K}
    (hz : IsNilpotent z) (hy : IsNilpotent y) (h : ζ • (1 + z) = 1 + y) : ζ = 1 := by
  have hy' : y = (ζ - 1) • (1 : Matrix ι ι K) + ζ • z := by
    have : y = ζ • (1 + z) - 1 := by rw [h]; abel
    rw [this, smul_add, sub_smul, one_smul]; abel
  have hc : Commute y (ζ • z) := by
    rw [hy']
    refine Commute.add_left ?_ (Commute.refl _)
    exact (Commute.one_left _).smul_left _
  have hn : IsNilpotent (y - ζ • z) := hc.isNilpotent_sub hy (hz.smul ζ)
  have : y - ζ • z = (ζ - 1) • (1 : Matrix ι ι K) := by rw [hy']; abel
  rw [this, spIsNilpotent_smul_one_iff] at hn
  exact sub_eq_zero.1 hn

theorem spIsNilpotent_conj {A Ainv X : Matrix ι ι K} (hA : A * Ainv = 1)
    (hA' : Ainv * A = 1) (hX : IsNilpotent X) : IsNilpotent (A * X * Ainv) := by
  obtain ⟨m, hm⟩ := hX
  refine ⟨m, ?_⟩
  have : ∀ k : ℕ, (A * X * Ainv) ^ k = A * X ^ k * Ainv := by
    intro k
    induction k with
    | zero => simp [hA]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc A * X ^ k * Ainv * (A * X * Ainv) = A * X ^ k * (Ainv * A) * X * Ainv := by
            simp only [mul_assoc]
        _ = A * (X ^ k * X) * Ainv := by rw [hA', mul_one]; simp only [mul_assoc]
  rw [this, hm]; simp

theorem sp_rank_one_eq {a b w ψ : ι → K} (hw : w ≠ 0) (hψ : ψ ≠ 0)
    (h : vecMulVec a ψ = vecMulVec w b) : ∃ c : K, a = c • w ∧ b = c • ψ := by
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h'; push Not at h'; exact hw (funext h')
  obtain ⟨j0, hj0⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra h'; push Not at h'; exact hψ (funext h')
  have hent : ∀ i j, a i * ψ j = w i * b j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [vecMulVec_apply] using this
  refine ⟨a i0 / w i0, ?_, ?_⟩
  · funext i
    have h1 := hent i j0
    have h2 := hent i0 j0
    have key : a i * w i0 = w i * a i0 := by
      apply mul_right_cancel₀ hj0
      linear_combination w i0 * h1 - w i * h2
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination key
  · funext j
    have h1 := hent i0 j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination -h1

theorem sp_vecMulVec_ne_zero {w ψ : ι → K} (hw : w ≠ 0) (hψ : ψ ≠ 0) : vecMulVec w ψ ≠ 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h'; push Not at h'; exact hw (funext h')
  obtain ⟨j0, hj0⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra h'; push Not at h'; exact hψ (funext h')
  intro h
  have := congrFun (congrFun h i0) j0
  simp [vecMulVec_apply] at this
  tauto

theorem sp_matrix_eq_zero_of_mulVec {M : Matrix ι ι K} (h : ∀ v, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem sp_add_smul_one_pow_prime_pow [Nonempty ι] {p : ℕ} [Fact p.Prime] [CharP K p]
    {B : Matrix ι ι K} {m : ℕ} (hB : B ^ m = 0) (c : K) :
    ∃ e : ℕ, (c • (1 : Matrix ι ι K) + B) ^ p ^ e = (c ^ p ^ e) • (1 : Matrix ι ι K) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, m ≤ p ^ e := ⟨m, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩
  refine ⟨e, ?_⟩
  rw [add_pow_char_pow_of_commute (R := Matrix ι ι K) p e
    ((Commute.one_left _).smul_left c), pow_eq_zero_of_le he hB, add_zero]
  rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one, map_pow]

end Generic

section FormJ

variable {r : ℕ} {K : Type} [Field K]

theorem spFormJ_transpose : (formJ r K)ᵀ = -formJ r K := by
  simp only [formJ, fromBlocks_transpose, transpose_zero, transpose_one, transpose_neg]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

theorem spFormJ_mul_self : formJ r K * formJ r K = -1 := by
  simp only [formJ, fromBlocks_multiply]
  simp
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

theorem spFormJ_mulVec_eq_zero {w : Fin r ⊕ Fin r → K} (h : formJ r K *ᵥ w = 0) : w = 0 := by
  have h1 : formJ r K *ᵥ (formJ r K *ᵥ w) = -w := by
    rw [mulVec_mulVec, spFormJ_mul_self, neg_mulVec, one_mulVec]
  rw [h, mulVec_zero] at h1
  exact neg_eq_zero.1 h1.symm

theorem spDot_formJ_self (w : Fin r ⊕ Fin r → K) : w ⬝ᵥ (formJ r K *ᵥ w) = 0 := by
  simp [dotProduct, Fintype.sum_sum_type, mulVec, formJ, fromBlocks, Matrix.one_apply]
  rw [add_neg_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem spDot_formJ_comm (u v : Fin r ⊕ Fin r → K) :
    u ⬝ᵥ (formJ r K *ᵥ v) = -(v ⬝ᵥ (formJ r K *ᵥ u)) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, spFormJ_transpose, neg_mulVec, neg_dotProduct,
    dotProduct_comm]

theorem spVecMul_formJ (w : Fin r ⊕ Fin r → K) : w ᵥ* formJ r K = -(formJ r K *ᵥ w) := by
  rw [← mulVec_transpose, spFormJ_transpose, neg_mulVec]

theorem spFormJ_mulVec_dot_comm (u v : Fin r ⊕ Fin r → K) :
    (formJ r K *ᵥ u) ⬝ᵥ v = -(u ⬝ᵥ (formJ r K *ᵥ v)) := by
  rw [dotProduct_comm, spDot_formJ_comm]

end FormJ

section SymX

variable {r : ℕ} {K : Type} [Field K]

@[expose] def symX (w w' : Fin r ⊕ Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  vecMulVec w' (formJ r K *ᵥ w) + vecMulVec w (formJ r K *ᵥ w')

theorem symX_mulVec (w w' x : Fin r ⊕ Fin r → K) :
    symX w w' *ᵥ x = ((formJ r K *ᵥ w) ⬝ᵥ x) • w' + ((formJ r K *ᵥ w') ⬝ᵥ x) • w := by
  simp [symX, add_mulVec, vecMulVec_mulVec]

theorem symX_mul_symX {w w' : Fin r ⊕ Fin r → K} (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) :
    symX w w' * symX w w' = 0 := by
  have h1 : (formJ r K *ᵥ w) ⬝ᵥ w' = 0 := by rw [spFormJ_mulVec_dot_comm, h, neg_zero]
  have h2 : (formJ r K *ᵥ w) ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact spDot_formJ_self w
  have h3 : (formJ r K *ᵥ w') ⬝ᵥ w' = 0 := by rw [dotProduct_comm]; exact spDot_formJ_self w'
  have h4 : (formJ r K *ᵥ w') ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact h
  simp only [symX, mul_add, add_mul, vecMulVec_mul_vecMulVec, h1, h2, h3, h4, zero_smul,
    vecMulVec_zero, add_zero]

theorem symX_transpose (w w' : Fin r ⊕ Fin r → K) :
    (symX w w')ᵀ = vecMulVec (formJ r K *ᵥ w) w' + vecMulVec (formJ r K *ᵥ w') w := by
  simp [symX, transpose_vecMulVec]

theorem symX_sp {w w' : Fin r ⊕ Fin r → K} (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) :
    (1 + symX w w')ᵀ * formJ r K * (1 + symX w w') = formJ r K := by
  have h1 : (formJ r K *ᵥ w) ⬝ᵥ w' = 0 := by rw [spFormJ_mulVec_dot_comm, h, neg_zero]
  have h2 : (formJ r K *ᵥ w) ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact spDot_formJ_self w
  have h3 : (formJ r K *ᵥ w') ⬝ᵥ w' = 0 := by rw [dotProduct_comm]; exact spDot_formJ_self w'
  have h4 : (formJ r K *ᵥ w') ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact h
  have e1 : (symX w w')ᵀ * formJ r K =
      -(vecMulVec (formJ r K *ᵥ w) (formJ r K *ᵥ w') +
        vecMulVec (formJ r K *ᵥ w') (formJ r K *ᵥ w)) := by
    rw [symX_transpose, add_mul, vecMulVec_mul, vecMulVec_mul, spVecMul_formJ, spVecMul_formJ,
      vecMulVec_neg, vecMulVec_neg, neg_add]
  have e2 : formJ r K * symX w w' =
      vecMulVec (formJ r K *ᵥ w') (formJ r K *ᵥ w) +
        vecMulVec (formJ r K *ᵥ w) (formJ r K *ᵥ w') := by
    rw [symX, mul_add, mul_vecMulVec, mul_vecMulVec]
  have e3 : (symX w w')ᵀ * formJ r K * symX w w' = 0 := by
    rw [e1]
    simp only [symX, neg_mul, add_mul, mul_add, vecMulVec_mul_vecMulVec, h1, h2, h3, h4,
      zero_smul, vecMulVec_zero, add_zero, neg_zero]
  calc (1 + symX w w')ᵀ * formJ r K * (1 + symX w w')
      = formJ r K + formJ r K * symX w w' + (symX w w')ᵀ * formJ r K +
        (symX w w')ᵀ * formJ r K * symX w w' := by
        rw [transpose_add, transpose_one]; noncomm_ring
    _ = formJ r K := by rw [e3, e1, e2]; abel

end SymX

section ConjSymX

variable {r : ℕ} {K : Type} [Field K]

theorem spConj_symX {A Ainv : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (hA : Aᵀ * formJ r K * A = μ • formJ r K) (h1 : A * Ainv = 1)
    (w w' : Fin r ⊕ Fin r → K) :
    μ • (A * symX w w' * Ainv) = symX (A *ᵥ w) (A *ᵥ w') := by
  have hJA : formJ r K * A = μ • (Ainvᵀ * formJ r K) := by
    calc formJ r K * A = (Ainvᵀ * Aᵀ) * formJ r K * A := by
          rw [← transpose_mul, h1, transpose_one, one_mul]
      _ = Ainvᵀ * (Aᵀ * formJ r K * A) := by simp only [Matrix.mul_assoc]
      _ = μ • (Ainvᵀ * formJ r K) := by rw [hA, Matrix.mul_smul]
  have key : ∀ v, μ • ((formJ r K *ᵥ v) ᵥ* Ainv) = formJ r K *ᵥ (A *ᵥ v) := by
    intro v
    rw [mulVec_mulVec, hJA, smul_mulVec, ← mulVec_mulVec, mulVec_transpose]
  simp only [symX, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, vecMulVec_mul, smul_add,
    ← vecMulVec_smul, key]

theorem spComp_formJ_mulVec (σ : K ≃+* K) (w : Fin r ⊕ Fin r → K) :
    σ ∘ (formJ r K *ᵥ w) = formJ r K *ᵥ (σ ∘ w) := by
  funext i
  have := RingHom.map_mulVec σ.toRingHom (formJ r K) w i
  have hJ : (formJ r K).map σ.toRingHom = formJ r K := formJ_map σ
  rw [hJ] at this
  exact this

theorem spMapMatrix_symX (σ : K ≃+* K) (w w' : Fin r ⊕ Fin r → K) :
    σ.toRingHom.mapMatrix (symX w w') = symX (σ ∘ w) (σ ∘ w') := by
  ext i j
  simp [symX, vecMulVec_apply, ← spComp_formJ_mulVec]

end ConjSymX

section Rad

variable {r : ℕ} {K : Type} [Field K]

@[expose] def kerN (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  LinearMap.ker N.mulVecLin

@[expose] def Wm (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  kerN N ⊓ LinearMap.range N.mulVecLin

theorem mem_kerN {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {x : Fin r ⊕ Fin r → K} :
    x ∈ kerN N ↔ N *ᵥ x = 0 := by
  simp [kerN]

theorem mem_Wm {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {x : Fin r ⊕ Fin r → K} :
    x ∈ Wm N ↔ N *ᵥ x = 0 ∧ ∃ v, N *ᵥ v = x := by
  simp [Wm, kerN]

theorem Wm_le_kerN (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) : Wm N ≤ kerN N :=
  inf_le_left

@[expose] def NilRad (N Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) : Prop :=
  (∀ x, Y *ᵥ x ∈ kerN N) ∧ (∀ x ∈ kerN N, Y *ᵥ x ∈ Wm N) ∧ (∀ x ∈ Wm N, Y *ᵥ x = 0)

variable {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

theorem NilRad.add {Y Y' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : NilRad N Y)
    (h' : NilRad N Y') : NilRad N (Y + Y') := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [add_mulVec]; exact add_mem (h.1 x) (h'.1 x)
  · rw [add_mulVec]; exact add_mem (h.2.1 x hx) (h'.2.1 x hx)
  · rw [add_mulVec, h.2.2 x hx, h'.2.2 x hx, add_zero]

theorem NilRad.neg {Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : NilRad N Y) :
    NilRad N (-Y) := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [neg_mulVec]; exact neg_mem (h.1 x)
  · rw [neg_mulVec]; exact neg_mem (h.2.1 x hx)
  · rw [neg_mulVec, h.2.2 x hx, neg_zero]

theorem NilRad.sub {Y Y' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : NilRad N Y)
    (h' : NilRad N Y') : NilRad N (Y - Y') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem NilRad.mul {Y Y' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : NilRad N Y)
    (h' : NilRad N Y') : NilRad N (Y * Y') := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← mulVec_mulVec]; exact Wm_le_kerN N (h.2.1 _ (h'.1 x))
  · rw [← mulVec_mulVec, h.2.2 _ (h'.2.1 x hx)]
    exact zero_mem _
  · rw [← mulVec_mulVec, h'.2.2 x hx, mulVec_zero]

theorem NilRad.triple {Y₁ Y₂ Y₃ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h₁ : NilRad N Y₁)
    (h₂ : NilRad N Y₂) (h₃ : NilRad N Y₃) : Y₁ * Y₂ * Y₃ = 0 := by
  apply sp_matrix_eq_zero_of_mulVec
  intro x
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact h₁.2.2 _ (h₂.2.1 _ (h₃.1 x))

theorem NilRad.cube {Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : NilRad N Y) :
    Y * Y * Y = 0 := h.triple h h

end Rad

section Unip

variable {r : ℕ} {K : Type} [Field K] {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

theorem spUnip_rel (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K) :
    formJ r K * N + Nᵀ * formJ r K + Nᵀ * formJ r K * N = 0 := by
  have h : formJ r K + (formJ r K * N + Nᵀ * formJ r K + Nᵀ * formJ r K * N) = formJ r K := by
    calc _ = (1 + N)ᵀ * formJ r K * (1 + N) := by
          rw [transpose_add, transpose_one]; noncomm_ring
      _ = formJ r K := hs
  exact add_eq_left.mp h

theorem spNtJ_ker (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K)
    {x : Fin r ⊕ Fin r → K} (hx : N *ᵥ x = 0) : Nᵀ *ᵥ (formJ r K *ᵥ x) = 0 := by
  have h := congrArg (fun M => M *ᵥ x) (spUnip_rel hs)
  simp only [add_mulVec, zero_mulVec, ← mulVec_mulVec, hx, mulVec_zero, add_zero, zero_add] at h
  exact h

theorem spDot_range_J_ker (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K)
    (v : Fin r ⊕ Fin r → K) {x : Fin r ⊕ Fin r → K} (hx : N *ᵥ x = 0) :
    (N *ᵥ v) ⬝ᵥ (formJ r K *ᵥ x) = 0 := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, spNtJ_ker hs hx, zero_dotProduct]

theorem spDot_ker_J_range (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K)
    {x : Fin r ⊕ Fin r → K} (v : Fin r ⊕ Fin r → K) (hx : N *ᵥ x = 0) :
    x ⬝ᵥ (formJ r K *ᵥ (N *ᵥ v)) = 0 := by
  rw [spDot_formJ_comm, spDot_range_J_ker hs v hx, neg_zero]

theorem spDot_W_J_ker (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K)
    {w w' : Fin r ⊕ Fin r → K} (hw : w ∈ Wm N) (hw' : w' ∈ kerN N) :
    w ⬝ᵥ (formJ r K *ᵥ w') = 0 := by
  obtain ⟨-, v, rfl⟩ := mem_Wm.1 hw
  exact spDot_range_J_ker hs v (mem_kerN.1 hw')

theorem symX_nilRad (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K)
    {w w' : Fin r ⊕ Fin r → K} (hw : w ∈ Wm N) (hw' : w' ∈ kerN N) : NilRad N (symX w w') := by
  obtain ⟨hwk, v, hv⟩ := mem_Wm.1 hw
  have hwk' : w ∈ kerN N := mem_kerN.2 hwk
  have hxw : ∀ x, N *ᵥ x = 0 → (formJ r K *ᵥ w) ⬝ᵥ x = 0 := by
    intro x hx
    rw [dotProduct_comm, ← hv]; exact spDot_ker_J_range hs v hx
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [symX_mulVec]; exact add_mem (Submodule.smul_mem _ _ hw') (Submodule.smul_mem _ _ hwk')
  · rw [symX_mulVec, hxw x (mem_kerN.1 hx), zero_smul, zero_add]
    exact Submodule.smul_mem _ _ hw
  · obtain ⟨hxk, u, hu⟩ := mem_Wm.1 hx
    rw [symX_mulVec, hxw x hxk, zero_smul, zero_add]
    have : (formJ r K *ᵥ w') ⬝ᵥ x = 0 := by
      rw [dotProduct_comm, ← hu]
      exact spDot_range_J_ker hs u (mem_kerN.1 hw')
    rw [this, zero_smul]

theorem N_symX (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K)
    {w w' : Fin r ⊕ Fin r → K} (hw : N *ᵥ w = 0) (hw' : N *ᵥ w' = 0) :
    N * symX w w' = 0 ∧ symX w w' * N = 0 := by
  constructor
  · rw [symX, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec, hw, hw']; simp
  · rw [symX, Matrix.add_mul, vecMulVec_mul, vecMulVec_mul, ← mulVec_transpose, ← mulVec_transpose,
      spNtJ_ker hs hw, spNtJ_ker hs hw']; simp

end Unip

section GenElt

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spGenGL (w w' : Fin r ⊕ Fin r → K) (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) :
    GL (Fin r ⊕ Fin r) K :=
  ⟨1 + symX w w', 1 - symX w w',
    by calc (1 + symX w w') * (1 - symX w w') = 1 - symX w w' * symX w w' := by noncomm_ring
        _ = 1 := by rw [symX_mul_symX h, sub_zero],
    by calc (1 - symX w w') * (1 + symX w w') = 1 - symX w w' * symX w w' := by noncomm_ring
        _ = 1 := by rw [symX_mul_symX h, sub_zero]⟩

theorem spGenGL_mem (w w' : Fin r ⊕ Fin r → K) (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) :
    spGenGL w w' h ∈ StatedSp r K :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.2 (symX_sp h)

@[expose] def spGen (w w' : Fin r ⊕ Fin r → K) (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) :
    StatedSp r K :=
  ⟨spGenGL w w' h, spGenGL_mem w w' h⟩

theorem coe_spGen (w w' : Fin r ⊕ Fin r → K) (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) :
    (((spGen w w' h : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + symX w w' := rfl

theorem spDot_mulVec_left {ι : Type*} [Fintype ι] (M : Matrix ι ι K) (w y : ι → K) :
    (M *ᵥ w) ⬝ᵥ y = w ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [dotProduct_mulVec, vecMul_transpose]

theorem spDot_sp (σ : StatedSp r K) (w w' : Fin r ⊕ Fin r → K) :
    (((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) ⬝ᵥ
      (formJ r K *ᵥ (((σ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w')) = w ⬝ᵥ (formJ r K *ᵥ w') := by
  have hσ := (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 σ.2)
  rw [spDot_mulVec_left, mulVec_mulVec, mulVec_mulVec, hσ]

theorem spConj_spGen (σ : StatedSp r K) (w w' : Fin r ⊕ Fin r → K)
    (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0) :
    σ * spGen w w' h * σ⁻¹ =
      spGen ((((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ w)
        ((((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ w')
        (by rw [spDot_sp, h]) := by
  have hσ := (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 σ.2)
  have h1 : (((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *
      ((((σ⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = 1 := by
    rw [← Units.val_mul]; simp
  apply Subtype.ext
  apply Units.ext
  show (((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *
      (1 + symX w w') * ((((σ⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) = 1 + symX _ _
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
  congr 1
  have := spConj_symX (A := (((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)))
    (Ainv := ((((σ⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))) (μ := 1) (by rw [one_smul]; exact hσ) h1 w w'
  rw [one_smul] at this
  exact this

end GenElt

section ProjEq

variable {r : ℕ} {K : Type} [Field K]

theorem sp_smul_of_proj_eq {a b : StatedSp r K} (h : proj r K a = proj r K b) :
    ∃ c : K, ((b : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      c • ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have h1 : a⁻¹ * b ∈ spScalars r K := QuotientGroup.eq.1 h
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(c : K), ?_⟩
  have h2 : b = a * (a⁻¹ * b) := by group
  have h3 : ((b : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (((a⁻¹ * b : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    conv_lhs => rw [h2]
    rfl
  rw [h3, ← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
    Matrix.mul_smul, Matrix.mul_one]

end ProjEq

section Model

variable {r : ℕ} {K : Type} [Field K]

@[expose] def modelGenC (r : ℕ) (K : Type) [Field K]
    (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) : Set (StatedProj (StatedSp r K)) :=
  {q | ∃ (w w' : Fin r ⊕ Fin r → K) (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0),
    w ∈ Wm N ∧ w' ∈ kerN N ∧ q = proj r K (spGen w w' h)}

theorem sp_hs {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (sg : StatedSp r K)
    (hsg : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N) :
    (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K := by
  have := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 sg.2
  rwa [hsg] at this

theorem model_h1C {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (sg : StatedSp r K)
    (hsg : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N)
    (q : StatedProj (StatedSp r K)) (hq : q ∈ modelGenC r K N) :
    proj r K sg * q = q * proj r K sg := by
  obtain ⟨w, w', h, hw, hw', rfl⟩ := hq
  have hs := sp_hs sg hsg
  obtain ⟨h1, h2⟩ := N_symX hs (mem_Wm.1 hw).1 (mem_kerN.1 hw')
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  show ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (1 + symX w w') = (1 + symX w w') *
      ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  rw [hsg]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h1, h2, add_zero]
  abel

theorem sp_commute_of_proj_commute [NeZero r] {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hN : IsNilpotent N) (sg : StatedSp r K)
    (hsg : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N)
    (σ : StatedSp r K) (h : proj r K σ * proj r K sg = proj r K sg * proj r K σ) :
    N * ((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * N := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, Nat.pos_of_neZero r⟩⟩
  rw [← map_mul, ← map_mul] at h
  obtain ⟨c, hc⟩ := sp_smul_of_proj_eq h
  have hσσ : ((σ⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K).val * (σ : GL (Fin r ⊕ Fin r) K).val
      = 1 := by rw [← Units.val_mul]; simp
  have hσσ' : (σ : GL (Fin r ⊕ Fin r) K).val *
      ((σ⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K).val = 1 := by
    rw [← Units.val_mul]; simp
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := (σ : GL (Fin r ⊕ Fin r) K).val with hM
  set Yi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((σ⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K).val with hYi
  have hc' : (1 + N) * M = c • (M * (1 + N)) := by
    have := hc
    simp only [Subgroup.coe_mul, Units.val_mul, hsg] at this
    exact this
  have key : c • (1 + N) = 1 + Yi * N * M := by
    have h1 : Yi * ((1 + N) * M) = c • (1 + N) := by
      rw [hc', Matrix.mul_smul, ← Matrix.mul_assoc, hYi, hσσ, Matrix.one_mul]
    have h2 : Yi * ((1 + N) * M) = Yi * M + Yi * N * M := by noncomm_ring
    rw [← h1, h2, hσσ]
  have hnil : IsNilpotent (Yi * N * M) := spIsNilpotent_conj hσσ hσσ' hN
  have hc1 : c = 1 := spEq_one_of_smul_one_add_nilpotent hN hnil key
  rw [hc1, one_smul] at hc'
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at hc'
  exact add_left_cancel hc'

end Model

section Model2

variable {r : ℕ} {K : Type} [Field K]

theorem model_hGenC [NeZero r] {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hN : IsNilpotent N)
    (sg : StatedSp r K)
    (hsg : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N)
    (t : StatedProj (StatedSp r K)) (ht : t * proj r K sg = proj r K sg * t)
    (q : StatedProj (StatedSp r K)) (hq : q ∈ modelGenC r K N) :
    t * q * t⁻¹ ∈ modelGenC r K N := by
  obtain ⟨σ, rfl⟩ := proj_surjective t
  have hc := sp_commute_of_proj_commute hN sg hsg σ ht
  obtain ⟨w, w', h, hw, hw', rfl⟩ := hq
  obtain ⟨hwk, v, hv⟩ := mem_Wm.1 hw
  refine ⟨((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w,
    ((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w',
    by rw [spDot_sp, h], ?_, ?_, ?_⟩
  · rw [mem_Wm]
    refine ⟨?_, ((σ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v, ?_⟩
    · rw [mulVec_mulVec, hc, ← mulVec_mulVec, hwk, mulVec_zero]
    · rw [mulVec_mulVec, hc, ← mulVec_mulVec, hv]
  · rw [mem_kerN, mulVec_mulVec, hc, ← mulVec_mulVec, mem_kerN.1 hw', mulVec_zero]
  · rw [← map_inv, ← map_mul, ← map_mul, spConj_spGen]

theorem model_hp3C [NeZero r] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs : (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K)
    (q : StatedProj (StatedSp r K)) (hq : q ∈ modelGenC r K N)
    (q' : StatedProj (StatedSp r K)) (hq' : q' ∈ modelGenC r K N) : (q' * q⁻¹) ^ p = 1 := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, Nat.pos_of_neZero r⟩⟩
  obtain ⟨w, w', h, hw, hw', rfl⟩ := hq
  obtain ⟨u, u', h2, hu, hu', rfl⟩ := hq'
  rw [← map_inv, ← map_mul, ← map_pow]
  have hX := symX_nilRad hs hw hw'
  have hX' := symX_nilRad hs hu hu'
  have hY : NilRad N (symX u u' - symX w w' - symX u u' * symX w w') :=
    (hX'.sub hX).sub (hX'.mul hX)
  have hY3 : (symX u u' - symX w w' - symX u u' * symX w w') ^ 3 = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]; exact hY.cube
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hpow : (spGen u u' h2 * (spGen w w' h)⁻¹) ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    show ((((spGen u u' h2 * (spGen w w' h)⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) ^ p = 1
    have hmat : ((((spGen u u' h2 * (spGen w w' h)⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        1 + (symX u u' - symX w w' - symX u u' * symX w w') := by
      show (1 + symX u u') * (1 - symX w w') = _
      noncomm_ring
    rw [hmat, add_pow_char_of_commute (R := Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) p
      (Commute.one_left _), one_pow, pow_eq_zero_of_le hp3 hY3, add_zero]
  rw [hpow, map_one]

end Model2

section UniqHelpers

variable {r : ℕ} {K : Type} [Field K]

theorem sp_exists_ne_zero_mem_Wm [NeZero r] {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hN : IsNilpotent N) (hN0 : N ≠ 0) : ∃ w, w ≠ 0 ∧ w ∈ Wm N := by
  classical
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, Nat.pos_of_neZero r⟩⟩
  have hex : ∃ m, N ^ m = 0 := hN
  set m := Nat.find hex with hm
  have hm0 : N ^ m = 0 := Nat.find_spec hex
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m = 0 ∨ m = 1 := by omega
    rcases this with h | h
    · rw [h, pow_zero] at hm0; exact one_ne_zero hm0
    · rw [h, pow_one] at hm0; exact hN0 hm0
  have hk : N ^ (m - 1) ≠ 0 := Nat.find_min hex (by omega)
  have hk2 : N ^ (m - 1 + 1) = 0 := by rw [show m - 1 + 1 = m by omega]; exact hm0
  by_contra hcon
  push Not at hcon
  apply hk
  apply sp_matrix_eq_zero_of_mulVec
  intro v
  by_contra hv
  refine hv ?_
  have hw : N ^ (m - 1) *ᵥ v ∈ Wm N := by
    rw [mem_Wm]
    refine ⟨?_, N ^ (m - 2) *ᵥ v, ?_⟩
    · rw [mulVec_mulVec, ← pow_succ', hk2, zero_mulVec]
    · rw [mulVec_mulVec, ← pow_succ']; congr 2; omega
  by_contra h
  exact hcon _ h hw

theorem conjAut_eq_one_of_scalarC {r : ℕ} {K : Type} [Field K] (P : gsp r K) {c : K}
    (hP : ((P : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      c • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) : conjAut r K P = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj]
  have hcomm : (P : GL (Fin r ⊕ Fin r) K) * (g : GL (Fin r ⊕ Fin r) K) =
      (g : GL (Fin r ⊕ Fin r) K) * (P : GL (Fin r ⊕ Fin r) K) := by
    apply Units.ext
    simp only [Units.val_mul, hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have : conjSp r K P g = g := Subtype.ext (by rw [coe_conjSp, hcomm, mul_inv_cancel_right])
  rw [this]; rfl

theorem spFixed_matrix {r : ℕ} {K : Type} [Field K] (A : gsp r K) (σ : K ≃+* K)
    (h : StatedSp r K)
    (hfix : (conjAut r K A * fieldAut r K σ) (proj r K h) = proj r K h) :
    ∃ ζ : K, ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      σ.toRingHom.mapMatrix ((h : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ζ • ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at hfix
  obtain ⟨ζ, hζ⟩ := sp_smul_of_proj_eq hfix.symm
  exact ⟨ζ, hζ⟩

end UniqHelpers

section Pair

variable {r : ℕ} {K : Type} [Field K]

theorem spPair_rel [NeZero r] (A : gsp r K) (σ : K ≃+* K) {μ : K}
    (hA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • formJ r K)
    (w w' : Fin r ⊕ Fin r → K) (h : w ⬝ᵥ (formJ r K *ᵥ w') = 0)
    (hfix : (conjAut r K A * fieldAut r K σ) (proj r K (spGen w w' h)) =
      proj r K (spGen w w' h)) :
    symX (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (σ ∘ w))
      (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (σ ∘ w')) =
      μ • symX w w' := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, Nat.pos_of_neZero r⟩⟩
  obtain ⟨ζ, hζ⟩ := spFixed_matrix A σ _ hfix
  rw [coe_spGen, map_add, map_one, spMapMatrix_symX] at hζ
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  set Ai : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAi
  have h1 : Am * Ai = 1 := (A : GL (Fin r ⊕ Fin r) K).mul_inv
  have h2 : Ai * Am = 1 := (A : GL (Fin r ⊕ Fin r) K).inv_mul
  have hXnil : IsNilpotent (symX w w') := ⟨2, by rw [pow_two]; exact symX_mul_symX h⟩
  have hXnil' : IsNilpotent (symX (σ ∘ w) (σ ∘ w')) := by
    rw [← spMapMatrix_symX]; exact hXnil.map σ.toRingHom.mapMatrix
  have hYnil : IsNilpotent (Am * symX (σ ∘ w) (σ ∘ w') * Ai) := spIsNilpotent_conj h1 h2 hXnil'
  have hconj : Am * (1 + symX (σ ∘ w) (σ ∘ w')) * Ai =
      1 + Am * symX (σ ∘ w) (σ ∘ w') * Ai := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
  rw [hconj] at hζ
  have hζ1 : ζ = 1 := spEq_one_of_smul_one_add_nilpotent hXnil hYnil hζ.symm
  rw [hζ1, one_smul] at hζ
  have hY : Am * symX (σ ∘ w) (σ ∘ w') * Ai = symX w w' := add_left_cancel hζ
  have := spConj_symX hA h1 (σ ∘ w) (σ ∘ w')
  rw [hY] at this
  exact this.symm

end Pair

section Uniq

variable {r : ℕ} {K : Type} [Field K]

theorem uniq_modelC {p : ℕ} [Fact p.Prime] [CharP K p] [Finite K] (hp2 : p ≠ 2) (hr : 3 ≤ r)
    {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hN : IsNilpotent N) (hN0 : N ≠ 0)
    (sg : StatedSp r K)
    (hsg : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N)
    (α : MulAut (StatedProj (StatedSp r K))) (hcop : (orderOf α).Coprime p)
    (hfixg : α (proj r K sg) = proj r K sg)
    (hfix : ∀ q ∈ modelGenC r K N, α q = q) : α = 1 := by
  have hrne : NeZero r := ⟨by omega⟩
  have hne : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hs := sp_hs sg hsg
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (K := K) hr).2 α
  obtain ⟨μu, hAμ⟩ := mem_gsp.1 A.2
  set μ : K := (μu : K) with hμdef
  have hμ0 : μ ≠ 0 := μu.ne_zero
  set Am : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  set Ai : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAi
  have h1 : Am * Ai = 1 := (A : GL (Fin r ⊕ Fin r) K).mul_inv
  have h2 : Ai * Am = 1 := (A : GL (Fin r ⊕ Fin r) K).inv_mul
  have hαfix : ∀ q ∈ modelGenC r K N, (conjAut r K A * fieldAut r K σ) q = q := fun q hq => by
    rw [← hα]; exact hfix q hq
  have hαg : (conjAut r K A * fieldAut r K σ) (proj r K sg) = proj r K sg := by
    rw [← hα]; exact hfixg
  obtain ⟨w0, hw0, hw0W⟩ := sp_exists_ne_zero_mem_Wm hN hN0
  have hw0k : w0 ∈ kerN N := Wm_le_kerN N hw0W
  have hpair : ∀ w ∈ Wm N, ∀ w' ∈ kerN N,
      symX (Am *ᵥ (σ ∘ w)) (Am *ᵥ (σ ∘ w')) = μ • symX w w' := by
    intro w hw w' hw'
    exact spPair_rel A σ hAμ w w' (spDot_W_J_ker hs hw hw')
      (hαfix _ ⟨w, w', spDot_W_J_ker hs hw hw', hw, hw', rfl⟩)
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)
  have hJw0 : formJ r K *ᵥ w0 ≠ 0 := fun h => hw0 (spFormJ_mulVec_eq_zero h)
  set u : Fin r ⊕ Fin r → K := Am *ᵥ (σ ∘ w0) with hu
  have hsymuu : ∀ z : Fin r ⊕ Fin r → K,
      symX z z = (2 : K) • vecMulVec z (formJ r K *ᵥ z) := by
    intro z; rw [symX, two_smul]
  have hA2 : vecMulVec u (formJ r K *ᵥ u) = vecMulVec w0 (μ • (formJ r K *ᵥ w0)) := by
    have hA1 := hpair w0 hw0W w0 hw0k
    rw [hsymuu, hsymuu] at hA1
    have h5 : (2 : K) • vecMulVec u (formJ r K *ᵥ u) =
        (2 : K) • vecMulVec w0 (μ • (formJ r K *ᵥ w0)) := by
      rw [vecMulVec_smul, smul_comm (2 : K) μ]; exact hA1
    exact smul_right_injective _ h2K h5
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero, zero_vecMulVec] at hA2
    exact sp_vecMulVec_ne_zero hw0 (smul_ne_zero hμ0 hJw0) hA2.symm
  have hJune : formJ r K *ᵥ u ≠ 0 := fun h => hune (spFormJ_mulVec_eq_zero h)
  obtain ⟨c, huc, hμc⟩ := sp_rank_one_eq hw0 hJune hA2
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hune; rw [huc, zero_smul]
  have hμ : μ = c * c := by
    rw [huc, mulVec_smul, smul_smul] at hμc
    exact smul_left_injective K hJw0 hμc
  have hB : ∀ w' ∈ kerN N, Am *ᵥ (σ ∘ w') = c • w' := by
    intro w' hw'
    have h := hpair w0 hw0W w' hw'
    set u' : Fin r ⊕ Fin r → K := Am *ᵥ (σ ∘ w') with hu'
    have e1 : symX u u' = c • (vecMulVec u' (formJ r K *ᵥ w0) +
        vecMulVec w0 (formJ r K *ᵥ u')) := by
      rw [symX, huc, mulVec_smul, vecMulVec_smul, smul_vecMulVec, smul_add]
    have e2 : μ • symX w0 w' = c • (c • (vecMulVec w' (formJ r K *ᵥ w0) +
        vecMulVec w0 (formJ r K *ᵥ w'))) := by
      rw [hμ, smul_smul, symX]
    rw [e1, e2] at h
    have hS := smul_right_injective _ hc0 h
    have key : vecMulVec (u' - c • w') (formJ r K *ᵥ w0) =
        vecMulVec w0 (-(formJ r K *ᵥ (u' - c • w'))) := by
      ext i j
      have := congrFun (congrFun hS i) j
      simp [vecMulVec_apply, mulVec_sub, mulVec_smul] at this ⊢
      linear_combination this
    obtain ⟨d, hzd, hzJ⟩ := sp_rank_one_eq hw0 hJw0 key
    rw [hzd, mulVec_smul] at hzJ
    have hd : d = 0 := by
      have h3 : d • (formJ r K *ᵥ w0) + d • (formJ r K *ᵥ w0) = 0 :=
        add_eq_zero_iff_eq_neg.2 hzJ.symm
      rw [← add_smul] at h3
      rcases smul_eq_zero.1 h3 with h4 | h4
      · have : (2 : K) * d = 0 := by rw [two_mul]; exact h4
        exact (mul_eq_zero.1 this).resolve_left h2K
      · exact absurd h4 hJw0
    rw [hd, zero_smul] at hzd
    exact sub_eq_zero.1 hzd
  have hσ : ∀ t, σ t = t := by
    intro t
    have h := hB (t • w0) (Submodule.smul_mem _ t hw0k)
    have e : σ ∘ (t • w0) = σ t • (σ ∘ w0) := by funext i; simp
    rw [e, mulVec_smul, ← hu, huc, smul_smul, smul_smul] at h
    have h' := smul_left_injective K hw0 h
    rw [mul_comm c t] at h'
    exact mul_right_cancel₀ hc0 h'
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  have hB' : ∀ w' ∈ kerN N, Am *ᵥ w' = c • w' := by
    intro w' hw'
    have := hB w' hw'
    have e : σ ∘ w' = w' := funext fun i => hσ _
    rwa [e] at this
  have hmap : ∀ M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, σ.toRingHom.mapMatrix M = M :=
    fun M => by ext i j; simp [hσ]
  have hAN : Am * N = N * Am := by
    obtain ⟨ζ, hζ⟩ := spFixed_matrix A σ sg hαg
    rw [hsg, map_add, map_one, hmap, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1] at hζ
    have hy : IsNilpotent (Am * N * Ai) := spIsNilpotent_conj h1 h2 hN
    have hζ1 : ζ = 1 := spEq_one_of_smul_one_add_nilpotent hN hy hζ.symm
    rw [hζ1, one_smul] at hζ
    have h3 := add_left_cancel hζ
    calc Am * N = (Am * N * Ai) * Am := by rw [Matrix.mul_assoc _ Ai, h2, Matrix.mul_one]
      _ = N * Am := by rw [h3]
  set B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := Am - c • 1 with hBdef
  have hBN : Commute B N := by
    show B * N = N * B
    rw [hBdef, sub_mul, mul_sub, hAN]
    simp
  have hBk : ∀ w' ∈ kerN N, B *ᵥ w' = 0 := by
    intro w' hw'
    rw [hBdef, sub_mulVec, smul_mulVec, one_mulVec, hB' w' hw', sub_self]
  obtain ⟨m, hm⟩ := hN
  have hBm : B ^ m = 0 := by
    apply sp_matrix_eq_zero_of_mulVec
    have key : ∀ k : ℕ, ∀ x, N ^ k *ᵥ x = 0 → B ^ k *ᵥ x = 0 := by
      intro k
      induction k with
      | zero => intro x hx; rw [pow_zero, one_mulVec] at hx ⊢; exact hx
      | succ k ih =>
        intro x hx
        rw [pow_succ, ← mulVec_mulVec] at hx
        have h1 := ih _ hx
        have hcomm : B ^ k * N = N * B ^ k := (hBN.pow_left k).eq
        have h2 : N *ᵥ (B ^ k *ᵥ x) = 0 := by
          rw [mulVec_mulVec, ← hcomm, ← mulVec_mulVec, h1]
        rw [pow_succ', ← mulVec_mulVec]
        exact hBk _ (mem_kerN.2 h2)
    intro x
    exact key m x (by rw [hm, zero_mulVec])
  obtain ⟨e, he⟩ := sp_add_smul_one_pow_prime_pow (p := p) hBm c
  have hAmB : Am = c • 1 + B := by rw [hBdef]; abel
  have hα' : α = conjAut r K A := by rw [hα, hσ1, map_one, mul_one]
  have hpow : α ^ p ^ e = 1 := by
    rw [hα', ← map_pow]
    apply conjAut_eq_one_of_scalarC _ (c := c ^ p ^ e)
    show (((A : GL (Fin r ⊕ Fin r) K) ^ p ^ e : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
    rw [Units.val_pow_eq_pow_val, ← hAm, hAmB]
    exact he
  have hdvd : orderOf α ∣ p ^ e := orderOf_dvd_of_pow_eq_one hpow
  have h1' : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right e hcop) hdvd
  exact orderOf_eq_one_iff.1 h1'

end Uniq

section OrderP

variable {r : ℕ} {K : Type} [Field K]

theorem sp_exists_nilpotent_of_orderOf_eq [NeZero r] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (g : StatedProj (StatedSp r K)) (hg : orderOf g = p) :
    ∃ (sg : StatedSp r K) (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K),
      ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N ∧
        IsNilpotent N ∧ N ≠ 0 ∧ g = proj r K sg := by
  have hne : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, Nat.pos_of_neZero r⟩⟩
  obtain ⟨s0, rfl⟩ := proj_surjective g
  have hpow : proj r K (s0 ^ p) = 1 := by
    rw [map_pow, ← hg]; exact pow_orderOf_eq_one _
  have hmem : s0 ^ p ∈ spScalars r K := by rw [← ker_proj]; exact hpow
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
  obtain ⟨c, hc⟩ := hmem
  set S0 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((s0 : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hS0
  have hS0p : S0 ^ p = (c : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have : ((((s0 ^ p : StatedSp r K)) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = S0 ^ p := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    rw [← this, ← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal]
  have hspJ := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1
    (s0 ^ p).2
  have hcc : (c : K) * c = 1 := by
    have : ((((s0 ^ p : StatedSp r K)) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = S0 ^ p := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    rw [this, hS0p, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul] at hspJ
    exact smul_formJ_injective r (by rw [hspJ, one_smul])
  have hz : (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) ∈
      StatedSp r K := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff,
      Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
      transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, hcc, one_smul]
  set z : StatedSp r K := ⟨_, hz⟩ with hzdef
  have hzproj : proj r K z = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range]
    exact ⟨c, rfl⟩
  set sg : StatedSp r K := s0 * z with hsgdef
  have hsgmat : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (c : K) • S0 := by
    show S0 * (((Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one]
  have hsgp : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ^ p = 1 := by
    rw [hsgmat, smul_pow, hS0p, smul_smul]
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
    have : (c : K) ^ p * c = 1 := by
      rw [← pow_succ, hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul, pow_two, hcc,
        one_pow]
    rw [this, one_smul]
  refine ⟨sg, ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) - 1,
    by abel, ?_, ?_, ?_⟩
  · refine ⟨p, ?_⟩
    rw [sub_pow_char_of_commute p (Commute.one_right _), hsgp, one_pow, sub_self]
  · intro h0
    have h1 : ((sg : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 :=
      sub_eq_zero.1 h0
    have h2 : sg = 1 := Subtype.ext (Units.ext h1)
    have h3 : proj r K s0 = 1 := by
      have : proj r K sg = proj r K s0 := by rw [hsgdef, map_mul, hzproj, mul_one]
      rw [← this, h2, map_one]
    rw [h3, orderOf_one] at hg
    exact (Fact.out : p.Prime).one_lt.ne hg
  · rw [hsgdef, map_mul, hzproj, mul_one]

end OrderP

theorem defCharInnerCoreFreeFamC : DefCharInnerCoreFreeFam .C := by
  intro S _ _ hS hnab idx hidx hSe p hp hp2 hch x hx hxo H hH
  obtain ⟨r, q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hSe
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hpq : p = q.p := by simpa using hch.symm
  have hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField (⟨.C r q, hv⟩ :
    TauCeti.ValidLieTypeIndex)
  let K := ↥(TauCeti.ValidLieTypeIndex.fixedField (⟨.C r q, hv⟩ : TauCeti.ValidLieTypeIndex))
  let e : S ≃* StatedProj (StatedSp r K) :=
    e0.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
  have hKq : Nat.card K = q.p ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder]
  subst hpq
  have : Fact q.p.Prime := ⟨hp⟩
  have hchar : CharP K q.p := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := q.exponent) (by rw [← Nat.card_eq_fintype_card, hKq])
  have hr3 : 3 ≤ r := hrange.1
  have : NeZero r := ⟨by omega⟩
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple hS hnab
  obtain ⟨g, rfl⟩ := hx
  have hord : orderOf g = q.p := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) (conj_injective_of_center_eq_bot hZ) g]
    exact hxo
  have hord0 : orderOf (e g) = q.p := by rw [MulEquiv.orderOf_eq e g]; exact hord
  obtain ⟨sg, N, hsg, hN, hN0, hg0⟩ := sp_exists_nilpotent_of_orderOf_eq hp2 (e g) hord0
  have hs := sp_hs sg hsg
  refine gLAPPrimeCoreOf_eq_bot_of_framework hZ hp g
    {q' | e q' ∈ modelGenC r K N} {g} ?_ ?_ ?_ ?_ ?_ H hH _ rfl
  · rintro q' (hq' | hq')
    · apply e.injective
      rw [map_mul, map_mul, hg0]
      exact model_h1C sg hsg (e q') hq'
    · rw [Set.mem_singleton_iff.1 hq']
  · intro s q' hs' hq'
    rw [Set.mem_singleton_iff.1 hq']
    exact hs'
  · intro s q' hs' hq'
    have ht : e s * proj r K sg = proj r K sg * e s := by
      rw [← hg0, ← map_mul, ← map_mul, hs']
    have := model_hGenC hN sg hsg (e s) ht (e q') hq'
    show e (s * q' * s⁻¹) ∈ modelGenC r K N
    rw [map_mul, map_mul, map_inv]
    exact this
  · intro q' hq' q'' hq''
    apply e.injective
    rw [map_pow, map_mul, map_inv, map_one]
    exact model_hp3C hp2 hs (e q') hq' (e q'') hq''
  · intro α hα hfix
    have hcop : (orderOf (MulAut.congr e α)).Coprime q.p := by
      rw [MulEquiv.orderOf_eq (MulAut.congr e) α]; exact hα
    have hαg : α g = g := hfix g (Or.inr rfl)
    have h1 : MulAut.congr e α = 1 := by
      refine uniq_modelC hp2 hr3 hN hN0 sg hsg _ hcop ?_ ?_
      · rw [← hg0, MulAut.congr_apply]
        simp [hαg]
      · intro q0 hq0
        have hmem : e.symm q0 ∈ {q' | e q' ∈ modelGenC r K N} := by simpa using hq0
        have := hfix _ (Or.inl hmem)
        change e (α (e.symm q0)) = q0
        rw [this]; simp
    exact (MulAut.congr e).injective (by rw [h1, map_one])

end CFSG.HardMathSupport.Timmesfeld.DefChar
