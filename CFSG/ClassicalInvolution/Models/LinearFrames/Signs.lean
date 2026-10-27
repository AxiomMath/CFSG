module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.LinearPairs.Frame
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix Module

section ZMat

variable (K : Type) [Field K] (n : ℕ)

@[expose] def zMat (N : Finset (Fin n)) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun a => if a ∈ N then (-1 : K) else 1

variable {K n}

theorem zMat_apply_self (N : Finset (Fin n)) (a : Fin n) :
    zMat K n N a a = if a ∈ N then (-1 : K) else 1 := by
  simp [zMat]

theorem zMat_apply_of_ne (N : Finset (Fin n)) {a b : Fin n} (h : a ≠ b) : zMat K n N a b = 0 := by
  simp [zMat, Matrix.diagonal_apply_ne _ h]

theorem zMat_mul_self (N : Finset (Fin n)) : zMat K n N * zMat K n N = 1 := by
  rw [zMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem zMat_mul_comm (N N' : Finset (Fin n)) :
    zMat K n N * zMat K n N' = zMat K n N' * zMat K n N := by
  rw [zMat, zMat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem zMat_empty : zMat K n ∅ = 1 := by
  rw [zMat, ← Matrix.diagonal_one]
  congr 1

theorem zMat_inj (h2 : (2 : K) ≠ 0) {N N' : Finset (Fin n)} (h : zMat K n N = zMat K n N') :
    N = N' := by
  ext a
  have := congrFun (congrFun h a) a
  rw [zMat_apply_self, zMat_apply_self] at this
  by_cases ha : a ∈ N <;> by_cases ha' : a ∈ N' <;> simp_all
  · exact h2 (by linear_combination -this)
  · exact h2 (by linear_combination this)

theorem det_zMat (N : Finset (Fin n)) : (zMat K n N).det = (-1) ^ N.card := by
  rw [zMat, Matrix.det_diagonal]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  simp

theorem conjTr_zMat (σ : K ≃+* K) (N : Finset (Fin n)) :
    CFSG.LieType.Universal.Unitary.conjTr σ (zMat K n N) = zMat K n N := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [CFSG.LieType.Universal.Unitary.conjTr, zMat]
    split_ifs <;> simp
  · simp [CFSG.LieType.Universal.Unitary.conjTr, zMat, Matrix.diagonal_apply_ne _ hab,
      Matrix.diagonal_apply_ne _ (Ne.symm hab)]

theorem zMat_pair_mul {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    zMat K n {i, j} * zMat K n {j, k} = zMat K n {i, k} := by
  rw [zMat, zMat, zMat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases ha : a = i
  · subst ha
    simp [hij, hik]
  · by_cases ha' : a = j
    · subst ha'
      simp [hij.symm, hjk]
    · by_cases ha'' : a = k
      · subst ha''
        simp [hik.symm, hjk.symm]
      · simp [ha, ha', ha'']

end ZMat

section Eigen

variable {K : Type} [Field K] {n : ℕ}

theorem mem_eigSpace_zMat_neg_one (h2 : (2 : K) ≠ 0) {N : Finset (Fin n)} {v : Fin n → K} :
    v ∈ eigSpace (zMat K n N) (-1) ↔ ∀ a, a ∉ N → v a = 0 := by
  rw [mem_eigSpace_neg_one]
  constructor
  · intro h a ha
    have := congr_fun h a
    rw [zMat, Matrix.mulVec_diagonal] at this
    simp only [ha, ite_false, Pi.neg_apply, one_mul] at this
    have h' : (2 : K) * v a = 0 := by linear_combination this
    exact (mul_eq_zero.mp h').resolve_left h2
  · intro h
    funext a
    rw [zMat, Matrix.mulVec_diagonal]
    by_cases ha : a ∈ N
    · simp [ha]
    · simp [ha, h a ha]

theorem single_mem_eigSpace_zMat (h2 : (2 : K) ≠ 0) {N : Finset (Fin n)} {a : Fin n} (ha : a ∈ N)
    (c : K) : (Pi.single a c : Fin n → K) ∈ eigSpace (zMat K n N) (-1) := by
  rw [mem_eigSpace_zMat_neg_one h2]
  intro b hb
  have : b ≠ a := fun h => hb (h ▸ ha)
  simp [Pi.single_eq_of_ne this]

theorem finrank_eigSpace_zMat (h2 : (2 : K) ≠ 0) (N : Finset (Fin n)) :
    finrank K (eigSpace (zMat K n N) (-1)) = N.card := by
  classical
  set w : Fin n → K := fun a => if a ∈ N then 0 else 2 with hw
  have hker : eigSpace (zMat K n N) (-1) = LinearMap.ker (Matrix.toLin' (Matrix.diagonal w)) := by
    ext v
    rw [mem_eigSpace_zMat_neg_one h2, LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · intro h
      funext a
      rw [Matrix.mulVec_diagonal]
      by_cases ha : a ∈ N
      · simp [hw, ha]
      · simp [hw, ha, h a ha]
    · intro h a ha
      have := congr_fun h a
      rw [Matrix.mulVec_diagonal] at this
      simp only [hw, ha, ite_false, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left h2
  have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (Matrix.diagonal w))
  rw [← hker, Module.finrank_fin_fun] at hrank
  have hr : finrank K (LinearMap.range (Matrix.toLin' (Matrix.diagonal w))) =
      Fintype.card {a // w a ≠ 0} := by
    rw [← Matrix.rank_diagonal w]
    rfl
  have hc : Fintype.card {a // w a ≠ 0} = n - N.card := by
    have : Fintype.card {a // w a ≠ 0} = Fintype.card {a // a ∉ N} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
        by_cases ha : a ∈ N <;> simp [hw, ha, h2])
    rw [this, Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  have hNn : N.card ≤ n := by
    simpa using Finset.card_le_univ N
  omega

end Eigen

section SignGroup

variable {K : Type} [Field K] {n : ℕ}

@[expose] def IsSignDiag (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ d : Fin n → K, (∀ a, d a = 1 ∨ d a = -1) ∧ M = Matrix.diagonal d

theorem isSignDiag_one : IsSignDiag (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨1, fun _ => Or.inl rfl, Matrix.diagonal_one.symm⟩

theorem isSignDiag_zMat (N : Finset (Fin n)) : IsSignDiag (zMat K n N) :=
  ⟨fun a => if a ∈ N then -1 else 1, fun a => by dsimp only; split_ifs <;> simp, rfl⟩

theorem IsSignDiag.mul {M M' : Matrix (Fin n) (Fin n) K} (h : IsSignDiag M) (h' : IsSignDiag M') :
    IsSignDiag (M * M') := by
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨d', hd', rfl⟩ := h'
  refine ⟨fun a => d a * d' a, fun a => ?_, Matrix.diagonal_mul_diagonal d d'⟩
  rcases hd a with h | h <;> rcases hd' a with h' | h' <;> simp [h, h']

theorem IsSignDiag.mul_self {M : Matrix (Fin n) (Fin n) K} (h : IsSignDiag M) : M * M = 1 := by
  obtain ⟨d, hd, rfl⟩ := h
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases hd a with h | h <;> simp [h]

theorem IsSignDiag.mul_comm {M M' : Matrix (Fin n) (Fin n) K} (h : IsSignDiag M)
    (h' : IsSignDiag M') : M * M' = M' * M := by
  obtain ⟨d, -, rfl⟩ := h
  obtain ⟨d', -, rfl⟩ := h'
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact _root_.mul_comm _ _

theorem IsSignDiag.exists_zMat {M : Matrix (Fin n) (Fin n) K} (h : IsSignDiag M) :
    ∃ N : Finset (Fin n), M = zMat K n N := by
  classical
  obtain ⟨d, hd, rfl⟩ := h
  refine ⟨Finset.univ.filter fun a => d a = -1, ?_⟩
  rw [zMat]
  congr 1
  funext a
  rcases hd a with h | h <;> simp [h]

theorem IsSignDiag.eq_diagonal {M : Matrix (Fin n) (Fin n) K} (h : IsSignDiag M) :
    M = Matrix.diagonal fun a => M a a := by
  obtain ⟨d, -, rfl⟩ := h
  simp

theorem IsSignDiag.apply_self {M : Matrix (Fin n) (Fin n) K} (h : IsSignDiag M) (a : Fin n) :
    M a a = 1 ∨ M a a = -1 := by
  obtain ⟨d, hd, rfl⟩ := h
  simpa using hd a

theorem IsSignDiag.apply_of_ne {M : Matrix (Fin n) (Fin n) K} (h : IsSignDiag M) {a b : Fin n}
    (hab : a ≠ b) : M a b = 0 := by
  obtain ⟨d, -, rfl⟩ := h
  simp [Matrix.diagonal_apply_ne _ hab]

variable {G : Type*} [Group G] (mat : G →* Matrix (Fin n) (Fin n) K)

@[expose] def signSubgroup : Subgroup G where
  carrier := {x | IsSignDiag (mat x)}
  one_mem' := by simpa using (isSignDiag_one : IsSignDiag (1 : Matrix (Fin n) (Fin n) K))
  mul_mem' := fun {x y} hx hy => by
    simpa [map_mul] using (hx : IsSignDiag (mat x)).mul (hy : IsSignDiag (mat y))
  inv_mem' := by
    intro x hx
    have hx' : IsSignDiag (mat x) := hx
    have h1 : mat x⁻¹ * mat x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : mat x * mat x = 1 := hx'.mul_self
    have h3 : mat x⁻¹ = mat x := by
      calc mat x⁻¹ = mat x⁻¹ * (mat x * mat x) := by rw [h2, mul_one]
        _ = (mat x⁻¹ * mat x) * mat x := by rw [mul_assoc]
        _ = mat x := by rw [h1, one_mul]
    show IsSignDiag (mat x⁻¹)
    rw [h3]
    exact hx'

variable {mat}

theorem mem_signSubgroup {x : G} : x ∈ signSubgroup mat ↔ IsSignDiag (mat x) := Iff.rfl

theorem signSubgroup_sq (hinj : Function.Injective mat) {x : G} (hx : x ∈ signSubgroup mat) :
    x * x = 1 :=
  hinj (by rw [map_mul, map_one]; exact (mem_signSubgroup.mp hx).mul_self)

theorem signSubgroup_comm (hinj : Function.Injective mat) {x y : G} (hx : x ∈ signSubgroup mat)
    (hy : y ∈ signSubgroup mat) : x * y = y * x :=
  hinj (by rw [map_mul, map_mul]; exact (mem_signSubgroup.mp hx).mul_comm (mem_signSubgroup.mp hy))

end SignGroup

section Monomial

variable {K : Type} [Field K] {n : ℕ}

@[expose] def IsMonomialFor (M : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ k, ∃ a : K, a ≠ 0 ∧ M *ᵥ Pi.single k 1 = a • Pi.single (τ k) 1

theorem isMonomialFor_one : IsMonomialFor (1 : Matrix (Fin n) (Fin n) K) 1 := fun k =>
  ⟨1, one_ne_zero, by rw [Matrix.one_mulVec, one_smul]; rfl⟩

theorem IsMonomialFor.mul {M M' : Matrix (Fin n) (Fin n) K} {τ τ' : Equiv.Perm (Fin n)}
    (h : IsMonomialFor M τ) (h' : IsMonomialFor M' τ') : IsMonomialFor (M * M') (τ * τ') := by
  intro k
  obtain ⟨a', ha', h1⟩ := h' k
  obtain ⟨a, ha, h2⟩ := h (τ' k)
  refine ⟨a * a', mul_ne_zero ha ha', ?_⟩
  rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h2, smul_smul, _root_.mul_comm a' a]
  rfl

theorem IsMonomialFor.mul_diagonal {M : Matrix (Fin n) (Fin n) K} {τ : Equiv.Perm (Fin n)}
    (h : IsMonomialFor M τ) (d : Fin n → K) :
    M * Matrix.diagonal d = Matrix.diagonal (fun b => d (τ.symm b)) * M := by
  refine Matrix.ext_of_mulVec_single fun k => ?_
  obtain ⟨a, ha, hk⟩ := h k
  rw [Matrix.mulVec_single_one] at hk
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  funext x
  have hMk : M x k = a * (Pi.single (τ k) 1 : Fin n → K) x := by
    have := congr_fun hk x
    simpa [Matrix.col_apply] using this
  simp only [Matrix.col_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hMk]
  by_cases hx : x = τ k
  · subst hx
    simp [_root_.mul_comm]
  · simp [Pi.single_eq_of_ne hx]

theorem IsMonomialFor.inv_mul_diagonal_mul {M N : Matrix (Fin n) (Fin n) K}
    {τ : Equiv.Perm (Fin n)} (h : IsMonomialFor M τ) (hNM : N * M = 1) (d : Fin n → K) :
    N * Matrix.diagonal d * M = Matrix.diagonal (fun a => d (τ a)) := by
  have h1 := h.mul_diagonal (fun a => d (τ a))
  simp only [Equiv.apply_symm_apply] at h1
  calc N * Matrix.diagonal d * M = N * (Matrix.diagonal d * M) := by rw [Matrix.mul_assoc]
    _ = N * (M * Matrix.diagonal (fun a => d (τ a))) := by rw [h1]
    _ = Matrix.diagonal (fun a => d (τ a)) := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]

theorem IsMonomialFor.mul_diagonal_mul_inv {M N : Matrix (Fin n) (Fin n) K}
    {τ : Equiv.Perm (Fin n)} (h : IsMonomialFor M τ) (hMN : M * N = 1) (d : Fin n → K) :
    M * Matrix.diagonal d * N = Matrix.diagonal (fun b => d (τ.symm b)) := by
  rw [h.mul_diagonal d, Matrix.mul_assoc, hMN, Matrix.mul_one]

theorem IsMonomialFor.mul_zMat_mul_inv {M N : Matrix (Fin n) (Fin n) K}
    {τ : Equiv.Perm (Fin n)} (h : IsMonomialFor M τ) (hMN : M * N = 1) (T : Finset (Fin n)) :
    M * zMat K n T * N = zMat K n (T.map τ.toEmbedding) := by
  rw [zMat, h.mul_diagonal_mul_inv hMN, zMat]
  congr 1
  funext b
  simp only [Finset.mem_map_equiv]

theorem IsMonomialFor.of_mul_eq_one {M N : Matrix (Fin n) (Fin n) K} {τ : Equiv.Perm (Fin n)}
    (h : IsMonomialFor M τ) (hNM : N * M = 1) : IsMonomialFor N τ⁻¹ := by
  intro k
  obtain ⟨a, ha, hk⟩ := h (τ⁻¹ k)
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  have h1 : N *ᵥ (M *ᵥ Pi.single (τ⁻¹ k) 1) = Pi.single (τ⁻¹ k) 1 := by
    rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  have e : τ (τ⁻¹ k) = k := by simp
  rw [hk, e, Matrix.mulVec_smul] at h1
  rw [← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]

end Monomial

section Entries

variable {K : Type} [Field K] {n : ℕ} {G : Type*} [Group G] {mat : G →* Matrix (Fin n) (Fin n) K}

variable (mat) in
@[expose] def entOf (e : G) (a : Fin n) : K := mat e a a

theorem entOf_cases {e : G} (he : e ∈ signSubgroup mat) (a : Fin n) :
    entOf mat e a = 1 ∨ entOf mat e a = -1 :=
  (mem_signSubgroup.mp he).apply_self a

theorem entOf_mul_self {e : G} (he : e ∈ signSubgroup mat) (a : Fin n) :
    entOf mat e a * entOf mat e a = 1 := by
  rcases entOf_cases he a with h | h <;> rw [h] <;> simp

theorem mat_eq_diagonal {e : G} (he : e ∈ signSubgroup mat) :
    mat e = Matrix.diagonal (entOf mat e) :=
  (mem_signSubgroup.mp he).eq_diagonal

theorem entOf_mul {e f : G} (he : e ∈ signSubgroup mat) (hf : f ∈ signSubgroup mat) (a : Fin n) :
    entOf mat (e * f) a = entOf mat e a * entOf mat f a := by
  have h1 : mat (e * f) = Matrix.diagonal (fun a => entOf mat e a * entOf mat f a) := by
    rw [map_mul, mat_eq_diagonal he, mat_eq_diagonal hf, Matrix.diagonal_mul_diagonal]
  have h2 : entOf mat (e * f) a = mat (e * f) a a := rfl
  rw [h2, h1, Matrix.diagonal_apply_eq]

theorem entOf_ne_neg (h2 : (2 : K) ≠ 0) {e : G} (he : e ∈ signSubgroup mat) (a : Fin n) :
    entOf mat e a ≠ -entOf mat e a := by
  intro h
  have h1 : (2 : K) * entOf mat e a = 0 := by linear_combination h
  have h3 := entOf_mul_self he a
  rcases mul_eq_zero.mp h1 with h4 | h4
  · exact h2 h4
  · rw [h4] at h3
    simp at h3

theorem inv_eq_self_of_mem_signSubgroup (hinj : Function.Injective mat) {e : G}
    (he : e ∈ signSubgroup mat) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (signSubgroup_sq hinj he)

theorem conj_mem_signSubgroup {g : G} {τ : Equiv.Perm (Fin n)} (hg : IsMonomialFor (mat g) τ)
    {e : G} (he : e ∈ signSubgroup mat) :
    g⁻¹ * e * g ∈ signSubgroup mat ∧ ∀ a, entOf mat (g⁻¹ * e * g) a = entOf mat e (τ a) := by
  have hm : mat (g⁻¹ * e * g) = Matrix.diagonal fun a => entOf mat e (τ a) := by
    rw [map_mul, map_mul, mat_eq_diagonal he]
    exact hg.inv_mul_diagonal_mul (by rw [← map_mul, inv_mul_cancel, map_one]) _
  have hs : g⁻¹ * e * g ∈ signSubgroup mat :=
    ⟨fun a => entOf mat e (τ a), fun a => entOf_cases he _, hm⟩
  refine ⟨hs, fun a => ?_⟩
  have h2 : entOf mat (g⁻¹ * e * g) a = mat (g⁻¹ * e * g) a a := rfl
  rw [h2, hm, Matrix.diagonal_apply_eq]

end Entries

section Perm

variable {K : Type} [Field K] {n : ℕ}

theorem isMonomialFor_diagonal (d : Fin n → K) (hd : ∀ a, d a ≠ 0) :
    IsMonomialFor (Matrix.diagonal d) 1 := fun k =>
  ⟨d k, hd k, by
    ext i
    rw [Matrix.mulVec_diagonal]
    by_cases h : i = k
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]⟩

theorem isMonomialFor_permMatrixHom (τ : Equiv.Perm (Fin n)) :
    IsMonomialFor (Matrix.permMatrixHom (R := K) τ) τ := fun k =>
  ⟨1, one_ne_zero, by
    rw [Matrix.permMatrixHom_apply, Matrix.permMatrix_mulVec, one_smul]
    ext i
    simp [Pi.single_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]⟩

variable (K) in
@[expose] def permSign (τ : Equiv.Perm (Fin n)) : K :=
  (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : K)

theorem permSign_cases (τ : Equiv.Perm (Fin n)) : permSign K τ = 1 ∨ permSign K τ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [permSign, h]

theorem permSign_mul_self (τ : Equiv.Perm (Fin n)) : permSign K τ * permSign K τ = 1 := by
  rcases permSign_cases (K := K) τ with h | h <;> rw [h] <;> simp

variable (K) in
@[expose] def monoMat (τ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) K :=
  Matrix.permMatrixHom τ * Matrix.diagonal fun a => if a.val = 0 then permSign K τ else 1

theorem det_monoMat (hn : 0 < n) (τ : Equiv.Perm (Fin n)) : (monoMat K τ).det = 1 := by
  rw [monoMat, Matrix.det_mul, Matrix.det_diagonal, Matrix.permMatrixHom_apply,
    Matrix.det_permutation]
  have : ∏ a : Fin n, (if a.val = 0 then permSign K τ else 1) = permSign K τ := by
    rw [Finset.prod_eq_single (⟨0, hn⟩ : Fin n)]
    · simp
    · intro b _ hb
      have : b.val ≠ 0 := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  rw [this, Equiv.Perm.sign_inv]
  exact permSign_mul_self τ

theorem isMonomialFor_monoMat (τ : Equiv.Perm (Fin n)) : IsMonomialFor (monoMat K τ) τ := by
  have h := (isMonomialFor_permMatrixHom (K := K) τ).mul
    (isMonomialFor_diagonal (fun a : Fin n => if a.val = 0 then permSign K τ else 1) (fun a => by
      by_cases ha : a.val = 0
      · rw [ite_eq_left ha]
        intro h0
        have := permSign_mul_self (K := K) τ
        rw [h0] at this
        simp at this
      · rw [ite_eq_right ha]
        exact one_ne_zero))
  rwa [mul_one] at h

end Perm

section Pairs

variable {n : ℕ}

abbrev Pair (n : ℕ) := {T : Finset (Fin n) // T.card = 2}

@[expose] def Pair.map (σ : Equiv.Perm (Fin n)) (T : Pair n) : Pair n :=
  ⟨T.1.map σ.toEmbedding, by rw [Finset.card_map]; exact T.2⟩

theorem Pair.coe_map (σ : Equiv.Perm (Fin n)) (T : Pair n) :
    (Pair.map σ T).1 = T.1.map σ.toEmbedding := rfl

theorem exists_perm_of_injective {m : ℕ} (hm : m ≤ n) (y : Fin m → Fin n)
    (hy : Function.Injective y) :
    ∃ τ : Equiv.Perm (Fin n), ∀ a : Fin m, τ ⟨a.val, lt_of_lt_of_le a.isLt hm⟩ = y a := by
  let x : Fin m ↪ Fin n := ⟨fun a => ⟨a.val, lt_of_lt_of_le a.isLt hm⟩, fun a b h => by
    simpa [Fin.ext_iff] using h⟩
  obtain ⟨τ, hτ⟩ := (MulAction.isMultiplyPretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive (Fin n) m)) x ⟨y, hy⟩
  refine ⟨τ, fun a => ?_⟩
  exact congrArg (fun e : Fin m ↪ Fin n => e a) hτ

theorem exists_perm_pair (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin n), τ ⟨0, by omega⟩ = i ∧ τ ⟨1, by omega⟩ = j := by
  obtain ⟨τ, hτ⟩ := exists_perm_of_injective hn ![i, j] (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hij])
  exact ⟨τ, by simpa using hτ 0, by simpa using hτ 1⟩

theorem exists_perm_triple (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ∃ τ : Equiv.Perm (Fin n), τ ⟨0, by omega⟩ = i ∧ τ ⟨1, by omega⟩ = j ∧
      τ ⟨2, by omega⟩ = k := by
  obtain ⟨τ, hτ⟩ := exists_perm_of_injective hn ![i, j, k] (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm hij, Ne.symm hjk, Ne.symm hik])
  exact ⟨τ, by simpa using hτ 0, by simpa using hτ 1, by simpa using hτ 2⟩

theorem exists_pair_eq_of_mem {T : Finset (Fin n)} (hT : T.card = 2) {x : Fin n} (hx : x ∈ T) :
    ∃ i, i ≠ x ∧ T = {i, x} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact ⟨b, hab.symm, Finset.pair_comm _ _⟩
  · rw [Finset.mem_singleton] at hx'
    subst hx'
    exact ⟨a, hab, rfl⟩

theorem pair_disjoint_or_share_one {T T' : Finset (Fin n)} (hT : T.card = 2) (hT' : T'.card = 2)
    (hne : T ≠ T') :
    Disjoint T T' ∨ ∃ i j k : Fin n, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ T = {i, j} ∧ T' = {j, k} := by
  by_cases hd : Disjoint T T'
  · exact Or.inl hd
  · right
    obtain ⟨x, hx, hx'⟩ := Finset.not_disjoint_iff.mp hd
    obtain ⟨i, hix, hi⟩ := exists_pair_eq_of_mem hT hx
    obtain ⟨k, hkx, hk⟩ := exists_pair_eq_of_mem hT' hx'
    refine ⟨i, x, k, hix, hkx.symm, ?_, hi, by rw [hk, Finset.pair_comm]⟩
    rintro rfl
    exact hne (by rw [hi, hk])

@[expose] def weylGraph (n : ℕ) : SimpleGraph (Pair n) :=
  SimpleGraph.fromRel fun T T' => Disjoint T.1 T'.1

theorem weylGraph_adj {T T' : Pair n} :
    (weylGraph n).Adj T T' ↔ T ≠ T' ∧ Disjoint T.1 T'.1 := by
  rw [weylGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Or.inl h2⟩

end Pairs

end CFSG.ClassicalInvolution.Models
