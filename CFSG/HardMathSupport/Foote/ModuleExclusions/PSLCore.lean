module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInvLA
public import CFSG.Open.StatedAPI

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Matrix CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

section LA

variable {K : Type*} [Field K]

theorem exists_two_annihilators_fin {n : ℕ} (hn : 4 ≤ n) (v u : Fin n → K) :
    ∃ w₁ w₂ : Fin n → K, LinearIndependent K ![w₁, w₂] ∧ w₁ ⬝ᵥ v = 0 ∧ w₁ ⬝ᵥ u = 0 ∧
      w₂ ⬝ᵥ v = 0 ∧ w₂ ⬝ᵥ u = 0 := by
  let N : Matrix (Fin n) (Fin 2) K := Matrix.of fun i j => ![v, u] j i
  let Φ : (Fin n → K) →ₗ[K] (Fin 2 → K) := Matrix.vecMulLinear N
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  have h1 : Module.finrank K (LinearMap.range Φ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simpa using this
  have h2 : 1 < Module.finrank K (LinearMap.ker Φ) := by
    simp only [Module.finrank_fin_fun] at hrank
    omega
  have hpos : 0 < Module.finrank K (LinearMap.ker Φ) := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank h2 hx
  have hker : ∀ w : LinearMap.ker Φ, (w : Fin n → K) ⬝ᵥ v = 0 ∧ (w : Fin n → K) ⬝ᵥ u = 0 := by
    intro w
    have hw : Φ (w : Fin n → K) = 0 := w.2
    have e0 := congrFun hw 0
    have e1 := congrFun hw 1
    simp only [Φ, Matrix.vecMulLinear_apply, N, Matrix.vecMul, dotProduct, Matrix.of_apply,
      Pi.zero_apply] at e0 e1
    exact ⟨by simpa [dotProduct] using e0, by simpa [dotProduct] using e1⟩
  refine ⟨(x : Fin n → K), (y : Fin n → K), ?_, (hker x).1, (hker x).2, (hker y).1, (hker y).2⟩
  rw [LinearIndependent.pair_iff] at hy ⊢
  intro s t hst
  apply hy s t
  apply Subtype.ext
  simpa using hst

theorem exists_annihilator_fin {n : ℕ} (hn : 3 ≤ n) (v u : Fin n → K) :
    ∃ w : Fin n → K, w ≠ 0 ∧ w ⬝ᵥ v = 0 ∧ w ⬝ᵥ u = 0 := by
  let N : Matrix (Fin n) (Fin 2) K := Matrix.of fun i j => ![v, u] j i
  let Φ : (Fin n → K) →ₗ[K] (Fin 2 → K) := Matrix.vecMulLinear N
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  have h1 : Module.finrank K (LinearMap.range Φ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simpa using this
  have hpos : 0 < Module.finrank K (LinearMap.ker Φ) := by
    simp only [Module.finrank_fin_fun] at hrank
    omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hw : Φ (x : Fin n → K) = 0 := x.2
  have e0 := congrFun hw 0
  have e1 := congrFun hw 1
  simp only [Φ, Matrix.vecMulLinear_apply, N, Matrix.vecMul, dotProduct, Matrix.of_apply,
    Pi.zero_apply] at e0 e1
  refine ⟨(x : Fin n → K), fun h0 => hx (Subtype.ext h0), ?_, ?_⟩
  · simpa [dotProduct] using e0
  · simpa [dotProduct] using e1

end LA

section Core

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] {K : Type} [Field K] [CharP K 5]

theorem inverted_c55_proj_single (H : Subgroup (GL n K)) (Mu : GL n K) (hMH : Mu ∈ H)
    {X : Matrix n n K} (hXX : X * X = 0) (hX0 : X ≠ 0)
    (hMX : (Mu : Matrix n n K) * X = -(X * Mu)) {ζ : K} (hζ : ∀ a : ZMod 5, ζ ≠ zi K a)
    (hH : ∀ g : GL n K, ∀ a b : ZMod 5,
      (g : Matrix n n K) = 1 + zi K a • X + zi K b • (ζ • X) → g ∈ H) :
    ∃ Φ : C55 →* StatedProj H, Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H) * Φ u *
        (QuotientGroup.mk (⟨Mu, hMH⟩ : H) : StatedProj H)⁻¹ = (Φ u)⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hAA : X * X = 0 := hXX
  have hAB : X * (ζ • X) = 0 := by rw [Matrix.mul_smul, hXX, smul_zero]
  have hBA : (ζ • X) * X = 0 := by rw [Matrix.smul_mul, hXX, smul_zero]
  have hBB : (ζ • X) * (ζ • X) = 0 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hXX, smul_zero, smul_zero]
  have hMB : (Mu : Matrix n n K) * (ζ • X) = -((ζ • X) * Mu) := by
    rw [Matrix.mul_smul, hMX, Matrix.smul_mul, smul_neg]
  refine inverted_c55_proj H Mu hMH hAA hAB hBA hBB hMX hMB (fun a b => ?_) ?_
  · exact hH _ a b rfl
  · intro a b hab
    have h1 : (zi K a + zi K b * ζ) • X = 0 := by
      rw [add_smul, mul_smul]
      exact hab
    have h2 : zi K a + zi K b * ζ = 0 := (smul_eq_zero.mp h1).resolve_right hX0
    by_cases hb : b = 0
    · subst hb
      simp only [map_zero, zero_mul, add_zero] at h2
      exact ⟨(zi K).injective (by rw [h2, map_zero]), rfl⟩
    · exfalso
      have hb' : zi K b ≠ 0 := (map_ne_zero (zi K)).mpr hb
      apply hζ (-a * b⁻¹)
      have h3 : zi K (-a * b⁻¹) = -(zi K a) * (zi K b)⁻¹ := by
        have hneg : zi K (-a) = -zi K a := map_neg (zi K) a
        rw [_root_.map_mul, hneg, _root_.map_inv₀]
      rw [h3]
      field_simp
      linear_combination h2


omit [Nonempty n] in
theorem det_unip_eq_one {X : Matrix n n K} (hXX : X * X = 0) (ζ : K) (a b : ZMod 5) :
    (1 + zi K a • X + zi K b • (ζ • X)).det = 1 := by
  have hAB : X * (ζ • X) = 0 := by rw [Matrix.mul_smul, hXX, smul_zero]
  have hBA : (ζ • X) * X = 0 := by rw [Matrix.smul_mul, hXX, smul_zero]
  have hBB : (ζ • X) * (ζ • X) = 0 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hXX, smul_zero, smul_zero]
  exact det_Ehom_eq_one hXX hAB hBA hBB (Multiplicative.ofAdd (a, b))

end Core

section Eigen

variable {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]

theorem exists_mulVec_ne_zero {A : Matrix n n K} (h : A ≠ 0) : ∃ u : n → K, A *ᵥ u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  ext i j
  have := congrFun (hcon (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem exists_anticomm_nilp_of_sq_neg_one [CharP K 5] {M : Matrix n n K} (hM : M * M = (-1 : K) • 1)
    (hnon : ∀ a : K, M ≠ a • 1) :
    ∃ X : Matrix n n K, X * X = 0 ∧ X ≠ 0 ∧ M * X = -(X * M) := by
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  set P : Matrix n n K := M + (2 : K) • 1 with hP
  set Q : Matrix n n K := M - (2 : K) • 1 with hQ
  have hQP : Q * P = 0 := by
    set N : Matrix n n K := (2 : K) • 1 with hN
    have hc : Commute M N := (Commute.one_right M).smul_right 2
    have hNN : N * N = ((2 : K) * 2) • (1 : Matrix n n K) := by
      simp [hN, smul_smul]
    have h1 : Q * P = M * M - N * N := (hc.mul_self_sub_mul_self_eq').symm
    rw [h1, hNN, hM, ← sub_smul]
    have : (-1 : K) - 2 * 2 = 0 := by linear_combination (-1 : K) * h5
    rw [this, zero_smul]
  have hP0 : P ≠ 0 := fun h0 => hnon (-2) (by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h0)
  have hQ0 : Qᵀ ≠ 0 := fun h0 => hnon 2 (by
    have : Q = 0 := by simpa using h0
    exact sub_eq_zero.mp this)
  obtain ⟨u, hu⟩ := exists_mulVec_ne_zero hP0
  obtain ⟨y, hy⟩ := exists_mulVec_ne_zero hQ0
  set v : n → K := P *ᵥ u with hv
  set w : n → K := y ᵥ* Q with hw
  have hw' : Qᵀ *ᵥ y = w := by rw [hw, Matrix.mulVec_transpose]
  have hQv : Q *ᵥ v = 0 := by rw [hv, Matrix.mulVec_mulVec, hQP, Matrix.zero_mulVec]
  have hwP : w ᵥ* P = 0 := by rw [hw, Matrix.vecMul_vecMul, hQP, Matrix.vecMul_zero]
  have hMv : M *ᵥ v = (2 : K) • v := by
    have : Q *ᵥ v = M *ᵥ v - (2 : K) • v := by
      simp [hQ, Matrix.sub_mulVec, Matrix.smul_mulVec]
    rw [this] at hQv
    exact sub_eq_zero.mp hQv
  have hwM : w ᵥ* M = (-2 : K) • w := by
    have : w ᵥ* P = w ᵥ* M + (2 : K) • w := by
      simp [hP, Matrix.vecMul_add, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [this] at hwP
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hwP
  have hwv : w ⬝ᵥ v = 0 := by
    rw [hv, Matrix.dotProduct_mulVec, hwP, zero_dotProduct]
  refine ⟨Matrix.vecMulVec v w, ?_, ?_, ?_⟩
  · rw [Matrix.vecMulVec_mul_vecMulVec, hwv, zero_smul, Matrix.vecMulVec_zero]
  · intro h0
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (funext hc)
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hy (hw'.trans (funext hc))
    have := congrFun (congrFun h0 i) j
    simp [Matrix.vecMulVec_apply] at this
    tauto
  · rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hMv, hwM, Matrix.smul_vecMulVec,
      Matrix.vecMulVec_smul]
    module

end Eigen

section TwoByTwo

variable {K : Type} [Field K]

theorem sq_eq_neg_one_of_fin_two {M : Matrix (Fin 2) (Fin 2) K} {c : K} (hM : M * M = c • 1)
    (hdet : M.det = 1) (hnon : ∀ a : K, M ≠ a • 1) : c = -1 := by
  rw [Matrix.eta_fin_two M] at hM hdet hnon
  rw [Matrix.mul_fin_two, Matrix.smul_one_eq_diagonal] at hM
  rw [Matrix.det_fin_two_of] at hdet
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp at e00 e01 e10 e11
  set a := M 0 0
  set b := M 0 1
  set d := M 1 1
  set e := M 1 0
  have htr : a + d = 0 := by
    by_contra hne
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hne
    have he : e = 0 := by
      have : e * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hne
    have had : a = d := by
      have : (a - d) * (a + d) = 0 := by
        rw [hb, he] at e00 e11
        linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
    apply hnon a
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, he, had]
  have hd : d = -a := by linear_combination htr
  rw [hd] at hdet
  linear_combination (-1 : K) * hdet - e00

end TwoByTwo

section Main

variable {K : Type} [Field K] [CharP K 5]

omit [CharP K 5] in
theorem det_eq_one_of_mem_statedSL {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ StatedSL n K) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem psl_ge4_inverts {n : ℕ} (hn : 4 ≤ n) (z : StatedProj (StatedSL n K)) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) :
    ∃ Φ : C55 →* StatedProj (StatedSL n K), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹ := by
  classical
  have : NeZero n := ⟨by omega⟩
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc, hM⟩ := scalar_sq_of_mk_sq h hz2
  have hnon := not_scalar_of_mk_ne_one h hz1
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_not_scalar _ hnon
  obtain ⟨w₁, w₂, hw, h11, h12, h21, h22⟩ :=
    exists_two_annihilators_fin hn v
      (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
  set M : Matrix (Fin n) (Fin n) K := ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
  have hAA := invNil_mul M hM v w₁ w₁ h11 h12
  have hAB := invNil_mul M hM v w₁ w₂ h11 h12
  have hBA := invNil_mul M hM v w₂ w₁ h21 h22
  have hBB := invNil_mul M hM v w₂ w₂ h21 h22
  have hH : ∀ a b : ZMod 5, Tu hAA hAB hBA hBB (zi K a) (zi K b) ∈ StatedSL n K := fun a b =>
    Subgroup.subset_closure (det_Ehom_eq_one hAA hAB hBA hBB (Multiplicative.ofAdd (a, b)))
  have hind : ∀ a b : ZMod 5, zi K a • invNil M c v w₁ + zi K b • invNil M c v w₂ = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have h0 : invNil M c v (zi K a • w₁ + zi K b • w₂) = 0 := by
      rw [invNil_add, invNil_smul, invNil_smul]
      exact hab
    have h1 := eq_zero_of_invNil_eq_zero M c hv h0
    rw [LinearIndependent.pair_iff] at hw
    obtain ⟨ha, hb⟩ := hw _ _ h1
    exact ⟨(zi K).injective (by rw [ha, map_zero]), (zi K).injective (by rw [hb, map_zero])⟩
  exact inverted_c55_proj (StatedSL n K) (h : GL (Fin n) K) h.2 hAA hAB hBA hBB
    (mul_invNil M hc hM v w₁) (mul_invNil M hc hM v w₂) hH hind

theorem exists_not_mem_primeField (hK : 5 < Nat.card K) : ∃ ζ : K, ∀ a : ZMod 5, ζ ≠ zi K a := by
  by_contra hcon
  push Not at hcon
  have hs : Function.Surjective (zi K) := fun ζ => by
    obtain ⟨a, ha⟩ := hcon ζ
    exact ⟨a, ha.symm⟩
  have := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_zmod] at this
  omega

theorem psl_small_inverts {n : ℕ} (hn2 : 2 ≤ n) (hn3 : n ≤ 3) (hK : 5 < Nat.card K)
    (z : StatedProj (StatedSL n K)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∃ Φ : C55 →* StatedProj (StatedSL n K), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹ := by
  classical
  have : NeZero n := ⟨by omega⟩
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ⟩ := exists_not_mem_primeField hK
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc, hM⟩ := scalar_sq_of_mk_sq h hz2
  have hnon := not_scalar_of_mk_ne_one h hz1
  have hH : ∀ X : Matrix (Fin n) (Fin n) K, X * X = 0 → ∀ g : GL (Fin n) K, ∀ a b : ZMod 5,
      (g : Matrix (Fin n) (Fin n) K) = 1 + zi K a • X + zi K b • (ζ • X) → g ∈ StatedSL n K :=
    fun X hXX g a b hg =>
      Subgroup.subset_closure (by
        show (g : Matrix (Fin n) (Fin n) K).det = 1
        rw [hg]
        exact det_unip_eq_one hXX ζ a b)
  by_cases h3 : 3 ≤ n
  · obtain ⟨v, hv⟩ := exists_linearIndependent_of_not_scalar _ hnon
    obtain ⟨w, hw0, h1, h2⟩ :=
      exists_annihilator_fin h3 v (((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
    set M : Matrix (Fin n) (Fin n) K := ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
    have hXX := invNil_mul M hM v w w h1 h2
    have hX0 : invNil M c v w ≠ 0 := fun h0 => hw0 (eq_zero_of_invNil_eq_zero M c hv h0)
    exact inverted_c55_proj_single (StatedSL n K) (h : GL (Fin n) K) h.2 hXX hX0
      (mul_invNil M hc hM v w) hζ (hH _ hXX)
  · have hn : n = 2 := by omega
    subst hn
    set M : Matrix (Fin 2) (Fin 2) K := ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hMdef
    have hc1 : c = -1 :=
      sq_eq_neg_one_of_fin_two hM (det_eq_one_of_mem_statedSL h.2) hnon
    subst hc1
    obtain ⟨X, hXX, hX0, hMX⟩ := exists_anticomm_nilp_of_sq_neg_one hM hnon
    exact inverted_c55_proj_single (StatedSL 2 K) (h : GL (Fin 2) K) h.2 hXX hX0 hMX hζ
      (hH _ hXX)

theorem psl_inverts {n : ℕ} (hn : 2 ≤ n) (hK : 4 ≤ n ∨ 5 < Nat.card K)
    (z : StatedProj (StatedSL n K)) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∃ Φ : C55 →* StatedProj (StatedSL n K), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹ := by
  by_cases h4 : 4 ≤ n
  · exact psl_ge4_inverts h4 z hz1 hz2
  · exact psl_small_inverts hn (by omega) (hK.resolve_left h4) z hz1 hz2

end Main

end CFSG.HardMathSupport.Foote.ModuleExclusions
