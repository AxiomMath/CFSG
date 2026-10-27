module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.Mason73.L4OrderTwoPart
public import CFSG.CharacterTheory.Semidihedral.DefiningCharacteristicDimension
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowSemidihedral
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.Mason73

open Matrix

namespace SL2Witness

section Arithmetic

variable {q : ℕ}

theorem fac_two_sub_one_eq_of_one (hq : q % 4 = 1) (hq1 : 1 < q) :
    (q ^ 2 - 1).factorization 2 - 1 = (q - 1).factorization 2 := by
  have h := OrderTwoPart.fac_two_sq_sub_one (Nat.odd_iff.mpr (by omega)) hq1
  rw [OrderTwoPart.fac_two_add_one_of_one hq] at h
  omega

theorem fac_two_add_one_eq_of_three (hq : q % 4 = 3) :
    (q ^ 2 - 1).factorization 2 - 1 = (q + 1).factorization 2 := by
  have h := OrderTwoPart.fac_two_sq_sub_one (q := q) (Nat.odd_iff.mpr (by omega)) (by omega)
  rw [OrderTwoPart.fac_two_sub_one_of_three hq] at h
  omega

theorem two_pow_dvd_sub_one (hq : q % 4 = 1) (hq1 : 1 < q) :
    2 ^ ((q ^ 2 - 1).factorization 2 - 1) ∣ q - 1 := by
  rw [fac_two_sub_one_eq_of_one hq hq1]
  exact Nat.ordProj_dvd (q - 1) 2

theorem two_pow_dvd_add_one (hq : q % 4 = 3) :
    2 ^ ((q ^ 2 - 1).factorization 2 - 1) ∣ q + 1 := by
  rw [fac_two_add_one_eq_of_three hq]
  exact Nat.ordProj_dvd (q + 1) 2

theorem one_le_fac_two_sq_sub_one (hq : Odd q) (hq1 : 1 < q) :
    1 ≤ (q ^ 2 - 1).factorization 2 := by
  have h := OrderTwoPart.fac_two_sq_sub_one hq hq1
  have := OrderTwoPart.one_le_fac_two_add_one hq
  omega

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2

theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 :=
  ⟨q - 1, by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · zify [Nat.one_le_pow 2 q hq, hq]
      ring⟩

theorem sq_sub_one_eq_two_mul_add_one (t : ℕ) :
    (2 * t + 1) ^ 2 - 1 = 2 * (2 * t + 1 + 1) * t :=
  Nat.sub_eq_of_eq_add (by ring)

theorem sq_sub_one_eq_two_mul_sub_one (t : ℕ) :
    (2 * t + 1) ^ 2 - 1 = 2 * (2 * t + 1 - 1) * (t + 1) :=
  Nat.sub_eq_of_eq_add (by rw [show 2 * t + 1 - 1 = 2 * t by omega]; ring)

end Arithmetic

theorem exists_unit_orderOf {K : Type*} [Field K] [Finite K] {d : ℕ}
    (hd : d ∣ Nat.card K - 1) : ∃ t : Kˣ, orderOf t = d :=
  CFSG.BrauerLinearThree.exists_orderOf_eq_of_dvd_natCard (by rwa [Nat.card_units])

theorem pow_eq_neg_one_of_orderOf {K : Type*} [Field K] {t : Kˣ} {m : ℕ} (hm : 0 < m)
    (ht : orderOf t = 2 * m) : t ^ m = -1 := by
  apply CFSG.BrauerLinearThree.units_eq_neg_one_of_orderOf_eq_two
  have h := orderOf_pow_orderOf_div (x := t) (n := 2) (by rw [ht]; omega)
    (by rw [ht]; exact dvd_mul_right 2 m)
  rwa [ht, Nat.mul_div_cancel_left m two_pos] at h

theorem orderOf_eq_four_of_sq {G : Type*} [Group G] {x y : G} (hxy : x ^ 2 = y)
    (hy : orderOf y = 2) : orderOf x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x) ?_ ?_
  · simpa using h
  · rw [pow_one, hxy]
    intro h1
    rw [h1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hxy, ← hy, pow_orderOf_eq_one]

theorem orderOf_conj_eq {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply]
  exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

section SL2

variable (K : Type*) [Field K]

@[expose] def diagSL : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun t := ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    refine Subtype.ext ?_
    change !![((s * t : Kˣ) : K), 0; 0, (((s * t)⁻¹ : Kˣ) : K)] =
      !![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] * !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagSL_coe (t : Kˣ) :
    (diagSL K t : Matrix (Fin 2) (Fin 2) K) = !![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)] := rfl

theorem diagSL_injective : Function.Injective (diagSL K) := by
  intro s t h
  have h00 := congrArg (fun A : SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  exact Units.ext (by simpa [diagSL_coe] using h00)

theorem orderOf_diagSL (t : Kˣ) : orderOf (diagSL K t) = orderOf t :=
  orderOf_injective _ (diagSL_injective K) t

@[expose] def antiSL (b : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -((b⁻¹ : Kˣ) : K); (b : K), 0], by simp [Matrix.det_fin_two]⟩

theorem antiSL_coe (b : Kˣ) :
    (antiSL K b : Matrix (Fin 2) (Fin 2) K) = !![0, -((b⁻¹ : Kˣ) : K); (b : K), 0] := rfl

theorem antiSL_sq (b : Kˣ) :
    antiSL K b ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, antiSL_coe, CFSG.Semidihedral.OddFieldSL2.minusIdentity,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem orderOf_antiSL (h2 : (2 : K) ≠ 0) (b : Kˣ) : orderOf (antiSL K b) = 4 :=
  orderOf_eq_four_of_sq (antiSL_sq K b)
    (CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K h2)

theorem antiSL_mul_diagSL (b t : Kˣ) :
    antiSL K b * diagSL K t = diagSL K t⁻¹ * antiSL K b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiSL_coe, diagSL_coe, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem antiSL_conj_diagSL (b t : Kˣ) :
    antiSL K b * diagSL K t * (antiSL K b)⁻¹ = (diagSL K t)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, antiSL_mul_diagSL, map_inv]

end SL2

section Unitary

variable {K : Type*} [Field K]

theorem conj_unitary (σ : K →+* K) {B B' X G : Matrix (Fin 2) (Fin 2) K}
    (hB : (B.map σ)ᵀ * B = G) (hX : (X.map σ)ᵀ * G * X = G) (hB' : B * B' = 1) :
    ((B * X * B').map σ)ᵀ * (B * X * B') = 1 := by
  simp only [Matrix.map_mul, Matrix.transpose_mul]
  calc (B'.map σ)ᵀ * ((X.map σ)ᵀ * (B.map σ)ᵀ) * (B * X * B')
      = (B'.map σ)ᵀ * ((X.map σ)ᵀ * ((B.map σ)ᵀ * B) * X) * B' := by
        simp only [Matrix.mul_assoc]
    _ = (B'.map σ)ᵀ * G * B' := by rw [hB, hX]
    _ = (B'.map σ)ᵀ * ((B.map σ)ᵀ * B) * B' := by rw [hB]
    _ = ((B * B').map σ)ᵀ * (B * B') := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by
        rw [hB', Matrix.mul_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp

theorem gram_basis (σ : K →+* K) {r : K} (hr : σ r * r = -1) :
    ((!![1, 1; r, -r] : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * !![1, 1; r, -r] = !![0, 2; 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hr | linear_combination (-1 : K) * hr

theorem gram_diagonal (σ : K →+* K) {a b : K} (h1 : σ a * b = 1) (h2 : σ b * a = 1) :
    ((!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * !![0, 2; 2, 0] * !![a, 0; 0, b] =
      !![0, 2; 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination 2 * h1 | linear_combination 2 * h2

theorem gram_antidiagonal (σ : K →+* K) {a b : K} (h1 : σ a * b = 1) (h2 : σ b * a = 1) :
    ((!![0, a; b, 0] : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * !![0, 2; 2, 0] * !![0, a; b, 0] =
      !![0, 2; 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination 2 * h1 | linear_combination 2 * h2

theorem unitary_diagonal (σ : K →+* K) {a b : K} (h1 : σ a * a = 1) (h2 : σ b * b = 1) :
    ((!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * !![a, 0; 0, b] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | exact h1 | exact h2

theorem det_basis_ne_zero (h2 : (2 : K) ≠ 0) {r : K} (hr : r ≠ 0) :
    (!![1, 1; r, -r] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  intro h
  apply mul_ne_zero h2 hr
  linear_combination -h

theorem conj_unitary_GL (σ : K →+* K) (B X : GL (Fin 2) K) {G : Matrix (Fin 2) (Fin 2) K}
    (hB : ((B : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * (B : Matrix (Fin 2) (Fin 2) K) = G)
    (hX : ((X : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * G * (X : Matrix (Fin 2) (Fin 2) K) = G) :
    (((B * X * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ *
      ((B * X * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [Units.val_mul, Units.val_mul]
  exact conj_unitary σ hB hX (Units.mul_inv B)

theorem conj_rel_GL (B : GL (Fin 2) K) {A D : SpecialLinearGroup (Fin 2) K}
    (h : A * D * A⁻¹ = D⁻¹) :
    (B * SpecialLinearGroup.toGL A * B⁻¹) * (B * SpecialLinearGroup.toGL D * B⁻¹) *
        (B * SpecialLinearGroup.toGL A * B⁻¹)⁻¹ = (B * SpecialLinearGroup.toGL D * B⁻¹)⁻¹ := by
  have h' : SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL D *
      (SpecialLinearGroup.toGL A)⁻¹ = (SpecialLinearGroup.toGL D)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, h, map_inv]
  calc (B * SpecialLinearGroup.toGL A * B⁻¹) * (B * SpecialLinearGroup.toGL D * B⁻¹) *
        (B * SpecialLinearGroup.toGL A * B⁻¹)⁻¹
      = B * (SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL D *
          (SpecialLinearGroup.toGL A)⁻¹) * B⁻¹ := by group
    _ = B * (SpecialLinearGroup.toGL D)⁻¹ * B⁻¹ := by rw [h']
    _ = (B * SpecialLinearGroup.toGL D * B⁻¹)⁻¹ := by group

theorem det_conj_toGL (B : GL (Fin 2) K) (g : SpecialLinearGroup (Fin 2) K) :
    ((B * SpecialLinearGroup.toGL g * B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
    SpecialLinearGroup.coe_GL_coe_matrix, g.2, mul_one, ← Matrix.det_mul, Units.mul_inv,
    Matrix.det_one]

@[expose] def diagGL : Kˣ × Kˣ →* GL (Fin 2) K where
  toFun x := ⟨!![(x.1 : K), 0; 0, (x.2 : K)], !![((x.1⁻¹ : Kˣ) : K), 0; 0, ((x.2⁻¹ : Kˣ) : K)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagGL_coe (a b : Kˣ) :
    (diagGL (a, b) : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, (b : K)] := rfl

theorem diagGL_injective : Function.Injective (diagGL (K := K)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h00 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  have h11 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 1) h
  simp only [diagGL_coe] at h00 h11
  exact Prod.ext (Units.ext (by simpa using h00)) (Units.ext (by simpa using h11))

end Unitary

section UnitaryWitness

variable {K : Type} [Field K] (σ : K →+* K) {q : ℕ}

theorem iterate_eq_self [Finite K] (hK : Nat.card K = q ^ 2) (hσx : ∀ x : K, σ x = x ^ q) (x : K) :
    σ (σ x) = x := by
  have : Fintype K := Fintype.ofFinite K
  rw [hσx, hσx, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem map_pow_eq_map (hσx : ∀ x : K, σ x = x ^ q) (A : Matrix (Fin 2) (Fin 2) K) :
    A.map (· ^ q) = A.map σ := by
  ext i j
  simp [hσx]

theorem mem_statedSU (hσx : ∀ x : K, σ x = x ^ q) {g : GL (Fin 2) K}
    (hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1)
    (hunit : ((g : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1) :
    g ∈ Open.StatedSU 2 q K := by
  refine Subgroup.subset_closure ⟨hdet, ?_⟩
  change ((g : Matrix (Fin 2) (Fin 2) K).map (· ^ q))ᵀ * (g : Matrix (Fin 2) (Fin 2) K) = 1
  rw [map_pow_eq_map σ hσx]
  exact hunit

theorem exists_pow_add_one_eq_neg_one [Finite K] (hK : Nat.card K = q ^ 2) (hq : Odd q) :
    ∃ r : Kˣ, r ^ (q + 1) = -1 := by
  obtain ⟨t, rfl⟩ := hq
  obtain ⟨r, hr⟩ := exists_unit_orderOf (K := K) (d := 2 * (2 * t + 1 + 1)) (by
    rw [hK, sq_sub_one_eq_two_mul_add_one]
    exact dvd_mul_right _ _)
  exact ⟨r, pow_eq_neg_one_of_orderOf (by omega) hr⟩

theorem exists_pow_sub_one_eq_neg_one [Finite K] (hK : Nat.card K = q ^ 2) (hq : Odd q)
    (hq1 : 1 < q) :
    ∃ b : Kˣ, b ^ (q - 1) = -1 := by
  obtain ⟨t, rfl⟩ := hq
  obtain ⟨b, hb⟩ := exists_unit_orderOf (K := K) (d := 2 * (2 * t + 1 - 1)) (by
    rw [hK, sq_sub_one_eq_two_mul_sub_one]
    exact dvd_mul_right _ _)
  exact ⟨b, pow_eq_neg_one_of_orderOf (by omega) hb⟩

theorem map_mul_self_eq_neg_one (hσx : ∀ x : K, σ x = x ^ q) {r : Kˣ}
    (hr : r ^ (q + 1) = -1) : σ (r : K) * r = -1 := by
  rw [hσx, ← pow_succ, ← Units.val_pow_eq_pow_val, hr, Units.val_neg, Units.val_one]

@[expose] noncomputable def basisGL (h2 : (2 : K) ≠ 0) (r : Kˣ) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; (r : K), -(r : K)]
    (det_basis_ne_zero h2 r.ne_zero)

theorem gram_basisGL (h2 : (2 : K) ≠ 0) (hσx : ∀ x : K, σ x = x ^ q) {r : Kˣ}
    (hr : r ^ (q + 1) = -1) :
    ((basisGL h2 r : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * (basisGL h2 r : Matrix (Fin 2) (Fin 2) K) =
      !![0, 2; 2, 0] :=
  gram_basis σ (map_mul_self_eq_neg_one σ hσx hr)

theorem exists_unitary_core [Finite K] (hK : Nat.card K = q ^ 2) (hq : q % 4 = 1)
    (hσx : ∀ x : K, σ x = x ^ q) :
    ∃ x : GL (Fin 2) K,
      ((x : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * (x : Matrix (Fin 2) (Fin 2) K) = 1 ∧
      orderOf x = 2 ^ (q ^ 2 - 1).factorization 2 := by
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; exact hqodd.pow)
  obtain ⟨r, hr⟩ := exists_pow_add_one_eq_neg_one hK hqodd
  obtain ⟨lam, hlam⟩ := exists_unit_orderOf (K := K) (d := 2 ^ (q ^ 2 - 1).factorization 2)
    (by rw [hK]; exact Nat.ordProj_dvd _ 2)
  have hσlam0 : σ (lam : K) ≠ 0 := (map_ne_zero σ).mpr lam.ne_zero
  have h1 : σ (lam : K) * (((lam ^ q)⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← hσx]
    exact mul_inv_cancel₀ hσlam0
  have h1' : σ (((lam ^ q)⁻¹ : Kˣ) : K) * lam = 1 := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← hσx, map_inv₀,
      iterate_eq_self σ hK hσx]
    exact inv_mul_cancel₀ lam.ne_zero
  refine ⟨basisGL h2 r * diagGL (lam, (lam ^ q)⁻¹) * (basisGL h2 r)⁻¹, ?_, ?_⟩
  · refine conj_unitary_GL σ _ _ (gram_basisGL σ h2 hσx hr) ?_
    rw [diagGL_coe]
    exact gram_diagonal σ h1 h1'
  · rw [orderOf_conj_eq, orderOf_injective _ diagGL_injective, Prod.orderOf_mk, hlam]
    refine Nat.lcm_eq_left (orderOf_dvd_of_pow_eq_one ?_)
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul, ← hlam, pow_orderOf_eq_one, one_pow, inv_one]

theorem exists_su2_core [Finite K] (hK : Nat.card K = q ^ 2) (hq : Odd q) (hq1 : 1 < q)
    (hσx : ∀ x : K, σ x = x ^ q) :
    ∃ R S : Open.StatedSU 2 q K,
      orderOf R = 2 ^ ((q ^ 2 - 1).factorization 2 - 1) ∧ orderOf S = 4 ∧ S * R * S⁻¹ = R⁻¹ := by
  have h2 : (2 : K) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; exact hq.pow)
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with hq4 | hq4
  ·
    obtain ⟨r, hr⟩ := exists_pow_add_one_eq_neg_one hK hq
    obtain ⟨b, hb⟩ := exists_pow_sub_one_eq_neg_one hK hq hq1
    have hσb : σ (b : K) = -b := by
      rw [hσx, show q = q - 1 + 1 by omega, pow_succ, ← Units.val_pow_eq_pow_val, hb,
        Units.val_neg, Units.val_one, neg_one_mul]
    obtain ⟨ρ, hρ⟩ := exists_unit_orderOf (K := K)
      (d := 2 ^ ((q ^ 2 - 1).factorization 2 - 1))
      (by rw [hK]; exact (two_pow_dvd_sub_one hq4 hq1).trans (sub_one_dvd_sq_sub_one q))
    have hρ1 : ρ ^ (q - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hρ]; exact two_pow_dvd_sub_one hq4 hq1)
    have hσρ : σ (ρ : K) = ρ := by
      rw [hσx, show q = q - 1 + 1 by omega, pow_succ, ← Units.val_pow_eq_pow_val, hρ1,
        Units.val_one, one_mul]
    have hσρ' : σ ((ρ⁻¹ : Kˣ) : K) = ((ρ⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hσρ]
    have hB := gram_basisGL σ h2 hσx hr
    have hR : basisGL h2 r * SpecialLinearGroup.toGL (diagSL K ρ) * (basisGL h2 r)⁻¹ ∈
        Open.StatedSU 2 q K :=
      mem_statedSU σ hσx (det_conj_toGL _ _) (conj_unitary_GL σ _ _ hB (by
        rw [SpecialLinearGroup.coe_GL_coe_matrix, diagSL_coe]
        exact gram_diagonal σ (by rw [hσρ]; exact Units.mul_inv ρ)
          (by rw [hσρ']; exact Units.inv_mul ρ)))
    have hS : basisGL h2 r * SpecialLinearGroup.toGL (antiSL K b) * (basisGL h2 r)⁻¹ ∈
        Open.StatedSU 2 q K :=
      mem_statedSU σ hσx (det_conj_toGL _ _) (conj_unitary_GL σ _ _ hB (by
        rw [SpecialLinearGroup.coe_GL_coe_matrix, antiSL_coe]
        refine gram_antidiagonal σ ?_ ?_
        · rw [map_neg, Units.val_inv_eq_inv_val, map_inv₀, hσb, inv_neg, neg_neg]
          exact inv_mul_cancel₀ b.ne_zero
        · rw [hσb, Units.val_inv_eq_inv_val, neg_mul_neg]
          exact mul_inv_cancel₀ b.ne_zero))
    refine ⟨⟨_, hR⟩, ⟨_, hS⟩, ?_, ?_, Subtype.ext (conj_rel_GL _ (antiSL_conj_diagSL K b ρ))⟩
    · rw [Subgroup.orderOf_mk, orderOf_conj_eq,
        orderOf_injective _ SpecialLinearGroup.toGL_injective, orderOf_diagSL, hρ]
    · rw [Subgroup.orderOf_mk, orderOf_conj_eq,
        orderOf_injective _ SpecialLinearGroup.toGL_injective, orderOf_antiSL K h2]
  ·
    obtain ⟨lam, hlam⟩ := exists_unit_orderOf (K := K)
      (d := 2 ^ ((q ^ 2 - 1).factorization 2 - 1))
      (by rw [hK]; exact (two_pow_dvd_add_one hq4).trans (add_one_dvd_sq_sub_one q))
    have hlam1 : lam ^ (q + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hlam]; exact two_pow_dvd_add_one hq4)
    have hσlam : σ (lam : K) * lam = 1 := by
      rw [hσx, ← pow_succ, ← Units.val_pow_eq_pow_val, hlam1, Units.val_one]
    have hσlam' : σ ((lam⁻¹ : Kˣ) : K) * ((lam⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hσlam, inv_one]
    have hR : SpecialLinearGroup.toGL (diagSL K lam) ∈ Open.StatedSU 2 q K :=
      mem_statedSU σ hσx
        (by rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact (diagSL K lam).2)
        (by
          rw [SpecialLinearGroup.coe_GL_coe_matrix, diagSL_coe]
          exact unitary_diagonal σ hσlam hσlam')
    have hS : SpecialLinearGroup.toGL (antiSL K 1) ∈ Open.StatedSU 2 q K :=
      mem_statedSU σ hσx
        (by rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact (antiSL K 1).2)
        (by
          rw [SpecialLinearGroup.coe_GL_coe_matrix, antiSL_coe]
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    have hrel := conj_rel_GL 1 (antiSL_conj_diagSL K 1 lam)
    simp only [one_mul, inv_one, mul_one] at hrel
    refine ⟨⟨_, hR⟩, ⟨_, hS⟩, ?_, ?_, Subtype.ext hrel⟩
    · rw [Subgroup.orderOf_mk, orderOf_injective _ SpecialLinearGroup.toGL_injective,
        orderOf_diagSL, hlam]
    · rw [Subgroup.orderOf_mk, orderOf_injective _ SpecialLinearGroup.toGL_injective,
        orderOf_antiSL K h2]

end UnitaryWitness

end SL2Witness

open SL2Witness

theorem exists_sl2_inverted_pair {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    ∃ R S : Matrix.SpecialLinearGroup (Fin 2) F,
      orderOf R = 2 ^ ((Nat.card F ^ 2 - 1).factorization 2 - 1) ∧
      orderOf S = 4 ∧ S * R * S⁻¹ = R⁻¹ := by
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hF
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hF) with hq | hq
  · obtain ⟨t, ht⟩ := exists_unit_orderOf (K := F) (two_pow_dvd_sub_one hq hq1)
    exact ⟨diagSL F t, antiSL F 1, by rw [orderOf_diagSL, ht], orderOf_antiSL F h2 1,
      antiSL_conj_diagSL F 1 t⟩
  · obtain ⟨T, u, w, -, -, -, hu, -, hw2, hinv⟩ :=
      CFSG.Semidihedral.DefiningCharacteristicDimension.exists_native_inverted_torus hF
    set k := (Nat.card F ^ 2 - 1).factorization 2 - 1 with hk
    set m := orderOf (u : SpecialLinearGroup (Fin 2) F) / 2 ^ k with hm
    have hdvd : 2 ^ k ∣ orderOf (u : SpecialLinearGroup (Fin 2) F) := by
      rw [hu]
      exact two_pow_dvd_add_one hq
    have hu0 : orderOf (u : SpecialLinearGroup (Fin 2) F) ≠ 0 := by
      rw [hu]
      exact Nat.succ_ne_zero _
    have hR : orderOf ((u : SpecialLinearGroup (Fin 2) F) ^ m) = 2 ^ k :=
      orderOf_pow_orderOf_div hu0 hdvd
    have hS : orderOf w = 4 :=
      orderOf_eq_four_of_sq hw2 (CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F h2)
    have hRS := hinv (u ^ m)
    rw [SubgroupClass.coe_pow] at hRS
    exact ⟨(u : SpecialLinearGroup (Fin 2) F) ^ m, w, hR, hS, hRS⟩

theorem exists_gl2_orderOf_two_pow {F : Type} [Field F] [Finite F] (hq : Nat.card F % 4 = 3) :
    ∃ x : GL (Fin 2) F, orderOf x = 2 ^ (Nat.card F ^ 2 - 1).factorization 2 := by
  have hν := one_le_fac_two_sq_sub_one (Nat.odd_iff.mpr (by omega)) (by omega : 1 < Nat.card F)
  obtain ⟨A, hA, -, -⟩ := CFSG.BrauerLinearThree.exists_nonsplit_element hq
    (m := (Nat.card F ^ 2 - 1).factorization 2 - 1)
    (by rw [Nat.sub_add_cancel hν]; exact Nat.ordProj_dvd _ 2)
  exact ⟨A, by rw [hA, Nat.sub_add_cancel hν]⟩

theorem exists_unitary_two_orderOf_two_pow {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) :
    ∃ x : GL (Fin 2) K,
      ((x : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 2) (Fin 2) K) = 1 ∧
      orderOf x = 2 ^ ((p ^ f) ^ 2 - 1).factorization 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hσx : ∀ x : K, iterateFrobenius K p f x = x ^ (p ^ f) := fun x =>
    iterateFrobenius_def p f x
  obtain ⟨x, hx, hord⟩ := exists_unitary_core (iterateFrobenius K p f) hK hq hσx
  exact ⟨x, by rw [map_pow_eq_map _ hσx]; exact hx, hord⟩

theorem exists_su2_inverted_pair {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f) (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ R S : Open.StatedSU 2 (p ^ f) K,
      orderOf R = 2 ^ (((p ^ f) ^ 2 - 1).factorization 2 - 1) ∧
      orderOf S = 4 ∧ S * R * S⁻¹ = R⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  exact exists_su2_core (iterateFrobenius K p f) hK (hp.eq_two_or_odd'.resolve_left hp2).pow
    (Nat.one_lt_pow hf.ne' hp.one_lt) (fun x => iterateFrobenius_def p f x)

end CFSG.LocalAnalysis.Mason73
