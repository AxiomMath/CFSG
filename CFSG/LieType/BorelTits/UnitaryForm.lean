module

public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.LieType.BorelTits.Matrix
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.BorelTits

open Matrix

section Unipotent

variable {F : Type} [Field F] (r : ℕ) [Fact r.Prime] [CharP F r]

theorem eq_one_of_pow_char_pow_eq_one {x : F} {e : ℕ} (hx : x ^ r ^ e = 1) : x = 1 := by
  have h : (x - 1) ^ r ^ e = 0 := by
    rw [sub_pow_char_pow, hx, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero e (Fact.out : r.Prime).ne_zero) |>.mp h)

include r in
theorem det_one_add_of_isNilpotent {ι : Type} [Fintype ι] [DecidableEq ι]
    {N : Matrix ι ι F} (hN : IsNilpotent N) : (1 + N).det = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Matrix.det_isEmpty
  obtain ⟨k, hk⟩ := hN
  obtain ⟨e, he⟩ : ∃ e : ℕ, k ≤ r ^ e := ⟨k, (Nat.lt_pow_self (Fact.out : r.Prime).one_lt).le⟩
  have hNe : N ^ r ^ e = 0 := by
    rw [← Nat.sub_add_cancel he, pow_add, hk, mul_zero]
  have hpow : (1 + N) ^ r ^ e = 1 := by
    rw [add_pow_char_pow_of_commute r e (Commute.one_left N), one_pow, hNe, add_zero]
  have := congrArg Matrix.det hpow
  rw [Matrix.det_pow, Matrix.det_one] at this
  exact eq_one_of_pow_char_pow_eq_one r this

end Unipotent

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

noncomputable abbrev unitaryInvolution : K ≃+* K :=
  iterateFrobeniusEquiv K p f

theorem unitaryInvolution_apply (c : K) : unitaryInvolution K p f c = c ^ p ^ f := by
  rw [unitaryInvolution, iterateFrobeniusEquiv_apply, iterateFrobenius_def]

variable {K p f}

theorem unitaryInvolution_involutive (hK : Nat.card K = (p ^ f) ^ 2) (c : K) :
    unitaryInvolution K p f (unitaryInvolution K p f c) = c := by
  have := Fintype.ofFinite K
  rw [unitaryInvolution_apply, unitaryInvolution_apply, ← pow_mul, ← sq, ← hK,
    Nat.card_eq_fintype_card, FiniteField.pow_card]

variable (p f) in
@[expose] noncomputable def unitaryForm (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) :
    ReflForm K (Fin n → K) where
  σ := unitaryInvolution K p f
  β u v := ∑ i, unitaryInvolution K p f (u i) * v i
  add_left u u' v := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  smul_left c u v := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]
  add_right u v v' := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c u v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  refl u v h := by
    have : unitaryInvolution K p f (∑ i, unitaryInvolution K p f (u i) * v i) = 0 := by
      rw [h, map_zero]
    rw [map_sum] at this
    simp only [map_mul, unitaryInvolution_involutive hK] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  nondeg u h := by
    funext i
    have := h (Pi.single i 1)
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at this
    exact (map_eq_zero_iff _ (unitaryInvolution K p f).injective).mp this

theorem unitaryForm_β (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (u v : Fin n → K) :
    (unitaryForm p f hK n).β u v = ∑ i, unitaryInvolution K p f (u i) * v i := rfl


open CFSG.Assembly.LowTwoRank

theorem unitaryForm_β_mulVec (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    (unitaryForm p f hK n).β (A *ᵥ u) (A *ᵥ v) =
      (unitaryInvolution K p f ∘ u) ⬝ᵥ
        (((A.map (unitaryInvolution K p f))ᵀ * A) *ᵥ v) := by
  rw [unitaryForm_β, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h : ∀ i, unitaryInvolution K p f ((A *ᵥ u) i) =
      ((A.map (unitaryInvolution K p f)) *ᵥ (unitaryInvolution K p f ∘ u)) i := by
    intro i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [dotProduct, h]

theorem unitaryForm_preserves_iff (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    (∀ u v, (unitaryForm p f hK n).β (A *ᵥ u) (A *ᵥ v) = (unitaryForm p f hK n).β u v) ↔
      (A.map (unitaryInvolution K p f))ᵀ * A = 1 := by
  constructor
  · intro h
    ext j k
    have hjk := h (Pi.single j 1) (Pi.single k 1)
    have lhs : (unitaryForm p f hK n).β (A *ᵥ Pi.single j 1) (A *ᵥ Pi.single k 1) =
        ((A.map (unitaryInvolution K p f))ᵀ * A) j k := by
      rw [unitaryForm_β, Matrix.mul_apply]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have rhs : (unitaryForm p f hK n).β (Pi.single j 1) (Pi.single k 1) =
        (1 : Matrix (Fin n) (Fin n) K) j k := by
      rw [unitaryForm_β, Matrix.one_apply]
      by_cases hjk' : j = k
      · subst hjk'
        simp [Pi.single_apply]
      · simp [Pi.single_apply, hjk', apply_ite]
        intro hkj
        exact hjk' hkj.symm
    rw [← lhs, hjk, rhs]
  · intro h u v
    rw [unitaryForm_β_mulVec, h, Matrix.one_mulVec, unitaryForm_β]
    rfl


theorem statedSU_preserves (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} {A : GL (Fin n) K}
    (hA : A ∈ StatedSU n (p ^ f) K) (u v : Fin n → K) :
    (unitaryForm p f hK n).β ((A : Matrix (Fin n) (Fin n) K) *ᵥ u)
      ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = (unitaryForm p f hK n).β u v := by
  induction hA using Subgroup.closure_induction generalizing u v with
  | mem A hA =>
    obtain ⟨-, h⟩ := hA
    have hmap : (A : Matrix (Fin n) (Fin n) K).map (unitaryInvolution K p f) =
        (A : Matrix (Fin n) (Fin n) K).map (· ^ p ^ f) := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply]
    exact (unitaryForm_preserves_iff hK _).mpr (hmap ▸ h) u v
  | one => simp
  | mul A B _ _ hA hB =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hB]
  | inv A _ hA =>
    rw [← hA]
    simp [Matrix.mulVec_mulVec]

theorem isIsometric_natRep_statedSU (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) :
    IsIsometric (unitaryForm p f hK n) (natRep (StatedSU n (p ^ f) K)) := by
  intro h u v
  rw [natRep_apply, natRep_apply]
  exact statedSU_preserves hK h.2 u v

theorem mkOfDetNeZero_mem_statedSU (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hM : ∀ u v, (unitaryForm p f hK n).β (M *ᵥ u) (M *ᵥ v) = (unitaryForm p f hK n).β u v) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero) ∈
      StatedSU n (p ^ f) K := by
  refine Subgroup.subset_closure ⟨hdet, ?_⟩
  have h := (unitaryForm_preserves_iff hK M).mp hM
  have hmap : M.map (unitaryInvolution K p f) = M.map (· ^ p ^ f) := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, unitaryInvolution_apply]
  rwa [hmap] at h


theorem unitaryForm_symm (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (u v : Fin n → K) :
    (unitaryForm p f hK n).β v u = unitaryInvolution K p f ((unitaryForm p f hK n).β u v) := by
  rw [unitaryForm_β, unitaryForm_β, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, unitaryInvolution_involutive hK, mul_comm]


omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem ReflForm.β_add_smul_add_smul {V : Type*} [AddCommGroup V] [Module K V]
    (F : ReflForm K V) (u v x : V) (a b : K) :
    F.β (u + a • x) (v + b • x) =
      F.β u v + b * F.β u x + F.σ a * F.β x v + F.σ a * b * F.β x x := by
  rw [F.add_left, F.add_right, F.add_right, F.smul_left, F.smul_left, F.smul_right,
    F.smul_right]
  ring

variable (p f) in
@[expose] noncomputable def unitaryTransvection {n : ℕ} (x : Fin n → K) (c : K) :
    Matrix (Fin n) (Fin n) K :=
  1 + c • vecMulVec x (unitaryInvolution K p f ∘ x)

theorem unitaryTransvection_mulVec (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (x v : Fin n → K)
    (c : K) :
    unitaryTransvection p f x c *ᵥ v = v + (c * (unitaryForm p f hK n).β x v) • x := by
  rw [unitaryTransvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, unitaryForm_β, op_smul_eq_smul, smul_smul]
  rfl

theorem unitaryTransvection_det (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} {x : Fin n → K}
    (hx : (unitaryForm p f hK n).β x x = 0) (c : K) :
    (unitaryTransvection p f x c).det = 1 := by
  rw [unitaryTransvection, ← Matrix.vecMulVec_smul, Matrix.vecMulVec_eq (Fin 1),
    Matrix.det_one_add_replicateCol_mul_replicateRow, smul_dotProduct, smul_eq_mul]
  have : (unitaryInvolution K p f ∘ x) ⬝ᵥ x = (unitaryForm p f hK n).β x x := rfl
  rw [this, hx, mul_zero, add_zero]


theorem unitaryTransvection_preserves (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} {x : Fin n → K}
    (hx : (unitaryForm p f hK n).β x x = 0) {c : K} (hc : unitaryInvolution K p f c = -c)
    (u v : Fin n → K) :
    (unitaryForm p f hK n).β (unitaryTransvection p f x c *ᵥ u)
      (unitaryTransvection p f x c *ᵥ v) = (unitaryForm p f hK n).β u v := by
  rw [unitaryTransvection_mulVec hK, unitaryTransvection_mulVec hK,
    ReflForm.β_add_smul_add_smul, hx, mul_zero, add_zero]
  have hσ : (unitaryForm p f hK n).σ = unitaryInvolution K p f := rfl
  rw [hσ, map_mul, hc, unitaryForm_symm hK x u]
  ring

theorem exists_mem_statedSU_transvection (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ}
    {x : Fin n → K} (hx : (unitaryForm p f hK n).β x x = 0) {c : K}
    (hc : unitaryInvolution K p f c = -c) :
    ∃ A ∈ StatedSU n (p ^ f) K, ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v =
      v + (c * (unitaryForm p f hK n).β x v) • x :=
  ⟨_, mkOfDetNeZero_mem_statedSU hK _ (unitaryTransvection_det hK hx c)
    (unitaryTransvection_preserves hK hx hc), fun v => unitaryTransvection_mulVec hK x v c⟩


variable (p f) in
@[expose] noncomputable def unitaryEichler {n : ℕ} (x y : Fin n → K) (c : K) :
    Matrix (Fin n) (Fin n) K :=
  1 + (vecMulVec (y + c • x) (unitaryInvolution K p f ∘ x) -
    vecMulVec x (unitaryInvolution K p f ∘ y))

theorem unitaryEichler_mulVec (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (x y v : Fin n → K)
    (c : K) :
    unitaryEichler p f x y c *ᵥ v = v + (unitaryForm p f hK n).β x v • (y + c • x) -
      (unitaryForm p f hK n).β y v • x := by
  rw [unitaryEichler, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sub_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul,
    add_sub_assoc]
  rfl

theorem unitaryEichler_preserves (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} {x y : Fin n → K}
    (hx : (unitaryForm p f hK n).β x x = 0) (hxy : (unitaryForm p f hK n).β x y = 0) {c : K}
    (hc : c + unitaryInvolution K p f c = -(unitaryForm p f hK n).β y y) (u v : Fin n → K) :
    (unitaryForm p f hK n).β (unitaryEichler p f x y c *ᵥ u)
      (unitaryEichler p f x y c *ᵥ v) = (unitaryForm p f hK n).β u v := by
  set F := unitaryForm p f hK n
  have hσ : F.σ = unitaryInvolution K p f := rfl
  have hyx : F.β y x = 0 := by rw [unitaryForm_symm hK x y, hxy, map_zero]
  have key : ∀ w : Fin n → K, unitaryEichler p f x y c *ᵥ w =
      w + F.β x w • y + (F.β x w * c - F.β y w) • x := by
    intro w
    rw [unitaryEichler_mulVec hK, smul_add, smul_smul, sub_smul]
    abel
  rw [key, key]
  simp only [F.add_left, F.add_right, F.smul_left, F.smul_right, hσ, hx, hxy, hyx, map_mul,
    map_sub, mul_zero, add_zero]
  rw [unitaryForm_symm hK x u, unitaryForm_symm hK y u]
  have hc' : unitaryInvolution K p f c = -F.β y y - c := by rw [← hc]; ring
  rw [hc']
  ring

theorem unitaryEichler_isNilpotent (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} {x y : Fin n → K}
    (hx : (unitaryForm p f hK n).β x x = 0) (hxy : (unitaryForm p f hK n).β x y = 0) (c : K) :
    IsNilpotent (unitaryEichler p f x y c - 1) := by
  set F := unitaryForm p f hK n
  have hyx : F.β y x = 0 := by rw [unitaryForm_symm hK x y, hxy, map_zero]
  set N := unitaryEichler p f x y c - 1 with hN
  have hNv : ∀ w, N *ᵥ w = F.β x w • (y + c • x) - F.β y w • x := by
    intro w
    rw [hN, Matrix.sub_mulVec, unitaryEichler_mulVec hK, Matrix.one_mulVec]
    abel
  have hNx : N *ᵥ x = 0 := by rw [hNv, hx, hyx, zero_smul, zero_smul, sub_zero]
  have hβx : ∀ w, F.β x (N *ᵥ w) = 0 := by
    intro w
    rw [hNv, F.β_sub_right, F.smul_right, F.smul_right, F.add_right, F.smul_right, hx, hxy]
    ring
  refine ⟨3, Matrix.toLin'.injective (LinearMap.ext fun w => ?_)⟩
  have h2 : N *ᵥ (N *ᵥ w) = (-(F.β x w * F.β y y)) • x := by
    rw [hNv (N *ᵥ w), hβx, zero_smul, zero_sub, hNv w, F.β_sub_right, F.smul_right,
      F.smul_right, F.add_right, F.smul_right, hyx, ← neg_smul]
    ring_nf
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.zero_mulVec, pow_succ, pow_succ, pow_one,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, hNx, smul_zero]


theorem exists_mem_statedSU_eichler (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} {x y : Fin n → K}
    (hx : (unitaryForm p f hK n).β x x = 0) (hxy : (unitaryForm p f hK n).β x y = 0) {c : K}
    (hc : c + unitaryInvolution K p f c = -(unitaryForm p f hK n).β y y) :
    ∃ A ∈ StatedSU n (p ^ f) K, ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v =
      v + (unitaryForm p f hK n).β x v • (y + c • x) - (unitaryForm p f hK n).β y v • x := by
  have hdet : (unitaryEichler p f x y c).det = 1 := by
    have := det_one_add_of_isNilpotent p (unitaryEichler_isNilpotent hK hx hxy c)
    rwa [add_sub_cancel] at this
  exact ⟨_, mkOfDetNeZero_mem_statedSU hK _ hdet (unitaryEichler_preserves hK hx hxy hc),
    fun v => unitaryEichler_mulVec hK x y v c⟩

theorem exists_unitaryInvolution_ne (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ a : K, unitaryInvolution K p f a ≠ a := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < p ^ f := by
    by_contra h
    have h1 : p ^ f ≤ 1 := not_lt.mp h
    have : Nat.card K ≤ 1 := by rw [hK]; nlinarith [Nat.zero_le (p ^ f)]
    exact absurd this (not_le.mpr Finite.one_lt_card)
  by_contra! h
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Polynomial.X ^ p ^ f - Polynomial.X : Polynomial K) (f := id) Function.injective_id
    (fun a => by simp [← unitaryInvolution_apply, h a])
    (by rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, ← Nat.card_eq_fintype_card, hK]
        nlinarith)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  rw [hP, Polynomial.natDegree_zero] at hdeg
  omega

theorem exists_unitaryInvolution_eq_neg (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ c : K, c ≠ 0 ∧ unitaryInvolution K p f c = -c := by
  obtain ⟨a, ha⟩ := exists_unitaryInvolution_ne hK
  refine ⟨a - unitaryInvolution K p f a, sub_ne_zero.mpr (Ne.symm ha), ?_⟩
  rw [map_sub, unitaryInvolution_involutive hK]
  ring

theorem exists_add_unitaryInvolution_eq (hK : Nat.card K = (p ^ f) ^ 2) {a : K}
    (ha : unitaryInvolution K p f a = a) : ∃ c : K, c + unitaryInvolution K p f c = a := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < p ^ f := by
    by_contra h
    have h1 : p ^ f ≤ 1 := not_lt.mp h
    have : Nat.card K ≤ 1 := by rw [hK]; nlinarith [Nat.zero_le (p ^ f)]
    exact absurd this (not_le.mpr Finite.one_lt_card)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : K, c₀ + unitaryInvolution K p f c₀ ≠ 0 := by
    by_contra! h
    have hdeg : (Polynomial.X ^ p ^ f + Polynomial.X : Polynomial K).natDegree = p ^ f := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;>
        simp [hq]
    have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.X ^ p ^ f + Polynomial.X : Polynomial K) (f := id) Function.injective_id
      (fun c => by
        have := h c
        simp only [unitaryInvolution_apply] at this
        simp [add_comm, this])
      (by rw [hdeg, ← Nat.card_eq_fintype_card, hK]; nlinarith)
    rw [hP, Polynomial.natDegree_zero] at hdeg
    omega
  set t := c₀ + unitaryInvolution K p f c₀ with ht
  have htσ : unitaryInvolution K p f t = t := by
    rw [ht, map_add, unitaryInvolution_involutive hK, add_comm]
  refine ⟨(a / t) * c₀, ?_⟩
  rw [map_mul, map_div₀, ha, htσ, ← mul_add, ← ht, div_mul_cancel₀ a hc₀]


end CFSG.LieType.BorelTits
