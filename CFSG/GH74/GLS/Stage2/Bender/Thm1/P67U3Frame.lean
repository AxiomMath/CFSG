module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Aut
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Characters

variable {K : Type} [Field K] {r : ℕ}

theorem u3f_pigeon (hr : r.Prime) {x₁ x₂ y₁ y₂ : K} (hx₂ : x₂ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hx : x₁ ^ r = x₂ ^ r) (hy : y₁ ^ r = y₂ ^ r) :
    ∃ m n : ℕ, ¬ (r ∣ m ∧ r ∣ n) ∧ x₁ ^ m * y₁ ^ n = x₂ ^ m * y₂ ^ n := by
  classical
  have hr0 : 0 < r := hr.pos
  set θ : K := x₁ / x₂ with hθ
  set η : K := y₁ / y₂ with hη
  have hθr : θ ^ r = 1 := by
    rw [hθ, div_pow, hx, div_self (pow_ne_zero _ hx₂)]
  have hηr : η ^ r = 1 := by
    rw [hη, div_pow, hy, div_self (pow_ne_zero _ hy₂)]
  have hmaps : Set.MapsTo (fun p : Fin r × Fin r => θ ^ (p.1 : ℕ) * η ^ (p.2 : ℕ))
      ((Finset.univ : Finset (Fin r × Fin r)) : Set (Fin r × Fin r))
      (Polynomial.nthRootsFinset r (1 : K) : Set K) := by
    intro p _
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hr0, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm (p.1 : ℕ), mul_comm (p.2 : ℕ), pow_mul, pow_mul, hθr, hηr]
    simp
  have hcard : (Polynomial.nthRootsFinset r (1 : K)).card <
      (Finset.univ : Finset (Fin r × Fin r)).card := by
    have h1 : (Polynomial.nthRootsFinset r (1 : K)).card ≤ r := by
      unfold Polynomial.nthRootsFinset
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots r 1)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    calc (Polynomial.nthRootsFinset r (1 : K)).card ≤ r := h1
      _ < r * r := by nlinarith [hr.one_lt]
  obtain ⟨⟨m, n⟩, -, ⟨m', n'⟩, -, hne, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hθ0 : θ ≠ 0 := fun h0 => by
    rw [h0, zero_pow hr.ne_zero] at hθr
    exact zero_ne_one hθr
  have hη0 : η ≠ 0 := fun h0 => by
    rw [h0, zero_pow hr.ne_zero] at hηr
    exact zero_ne_one hηr
  have hfeq' : θ ^ (m : ℕ) * η ^ (n : ℕ) = θ ^ (m' : ℕ) * η ^ (n' : ℕ) := hfeq
  have hm' : θ ^ (r - (m' : ℕ)) * θ ^ (m' : ℕ) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel m'.isLt.le, hθr]
  have hn' : η ^ (r - (n' : ℕ)) * η ^ (n' : ℕ) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel n'.isLt.le, hηr]
  refine ⟨(m : ℕ) + (r - (m' : ℕ)), (n : ℕ) + (r - (n' : ℕ)), ?_, ?_⟩
  · rintro ⟨hM, hN⟩
    apply hne
    have e1 := CFSG.GH74.GLS.Stage2.OddAut.eq_of_dvd_add_sub' m.isLt m'.isLt hM
    have e2 := CFSG.GH74.GLS.Stage2.OddAut.eq_of_dvd_add_sub' n.isLt n'.isLt hN
    rw [Fin.ext e1, Fin.ext e2]
  · have hx₁ : x₁ = θ * x₂ := by rw [hθ, div_mul_cancel₀ _ hx₂]
    have hy₁ : y₁ = η * y₂ := by rw [hη, div_mul_cancel₀ _ hy₂]
    have key : θ ^ ((m : ℕ) + (r - (m' : ℕ))) * η ^ ((n : ℕ) + (r - (n' : ℕ))) = 1 := by
      have hne0 : θ ^ (m' : ℕ) * η ^ (n' : ℕ) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hθ0) (pow_ne_zero _ hη0)
      apply mul_right_cancel₀ hne0
      calc θ ^ ((m : ℕ) + (r - (m' : ℕ))) * η ^ ((n : ℕ) + (r - (n' : ℕ))) *
            (θ ^ (m' : ℕ) * η ^ (n' : ℕ))
          = (θ ^ (m : ℕ) * η ^ (n : ℕ)) * ((θ ^ (r - (m' : ℕ)) * θ ^ (m' : ℕ)) *
              (η ^ (r - (n' : ℕ)) * η ^ (n' : ℕ))) := by
            rw [pow_add, pow_add]; ring
        _ = 1 * (θ ^ (m' : ℕ) * η ^ (n' : ℕ)) := by rw [hm', hn', hfeq']; ring
    rw [hx₁, hy₁, mul_pow, mul_pow]
    calc θ ^ ((m : ℕ) + (r - (m' : ℕ))) * x₂ ^ ((m : ℕ) + (r - (m' : ℕ))) *
          (η ^ ((n : ℕ) + (r - (n' : ℕ))) * y₂ ^ ((n : ℕ) + (r - (n' : ℕ))))
        = (θ ^ ((m : ℕ) + (r - (m' : ℕ))) * η ^ ((n : ℕ) + (r - (n' : ℕ)))) *
            (x₂ ^ ((m : ℕ) + (r - (m' : ℕ))) * y₂ ^ ((n : ℕ) + (r - (n' : ℕ)))) := by ring
      _ = _ := by rw [key, one_mul]

theorem u3f_fin3_cases : ∀ i j k x : Fin 3, i ≠ j → i ≠ k → j ≠ k → x = i ∨ x = j ∨ x = k := by
  decide

theorem u3f_exists_third : ∀ i j : Fin 3, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k := by
  decide

theorem u3f_char_ne (hr : r.Prime) {da db : Fin 3 → K} (hda : ∀ i, da i ≠ 0)
    (hdb : ∀ i, db i ≠ 0) (hra : ∀ i j, da i ^ r = da j ^ r) (hrb : ∀ i j, db i ^ r = db j ^ r)
    (hsc : ∀ m n : ℕ, (∀ i j, da i ^ m * db i ^ n = da j ^ m * db j ^ n) → r ∣ m ∧ r ∣ n)
    {i j : Fin 3} (hij : i ≠ j) : da i ≠ da j ∨ db i ≠ db j := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hdaij, hdbij⟩ := hcon
  obtain ⟨k, hik, hjk⟩ := u3f_exists_third i j hij
  obtain ⟨m, n, hmn, hv⟩ := u3f_pigeon hr (hda k) (hdb k) (hra i k) (hrb i k)
  apply hmn
  apply hsc m n
  have hall : ∀ x, da x ^ m * db x ^ n = da i ^ m * db i ^ n := by
    intro x
    rcases u3f_fin3_cases i j k x hij hik hjk with hx | hx | hx
    · rw [hx]
    · rw [hx, ← hdaij, ← hdbij]
    · rw [hx]; exact hv.symm
  intro x y
  rw [hall x, hall y]

end Characters

section Offdiag

variable {K : Type} [Field K] {r : ℕ} {σ : K →+* K}

theorem u3f_dual (hσ : ∀ c, σ (σ c) = c) {x y z : K} (h1 : σ x * y = 1) (h2 : σ y * z = 1) :
    z = x := by
  have h3 : x * σ y = 1 := by
    have := congrArg σ h1
    rwa [map_mul, hσ, map_one] at this
  have hy : σ y ≠ 0 := left_ne_zero_of_mul_eq_one h2
  apply mul_left_cancel₀ hy
  rw [h2, mul_comm, h3]

theorem u3f_cancel (hσ : ∀ c, σ (σ c) = c) {x y z : K} (h1 : σ x * z = 1) (h2 : σ y * z = 1) :
    x = y := by
  have hz : z ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have h3 : σ x = σ y := mul_right_cancel₀ hz (h1.trans h2.symm)
  rw [← hσ x, h3, hσ]

theorem u3f_rel {s g d : K} (hg : g ≠ 0) (h : s * g * d = g) : s * d = 1 := by
  apply mul_right_cancel₀ hg
  linear_combination h

theorem u3f_norm_aux (T U : K) (hn : σ T * T = 1) (hj : U * σ T = 1) : U = T := by
  apply mul_right_cancel₀ (left_ne_zero_of_mul_eq_one hn)
  rw [hj, mul_comm]
  exact hn.symm

theorem u3f_offdiag (hσ : ∀ c, σ (σ c) = c) (hr : r.Prime) {da db : Fin 3 → K}
    (hda : ∀ i, da i ≠ 0) (hdb : ∀ i, db i ≠ 0)
    (hra : ∀ i j, da i ^ r = da j ^ r) (hrb : ∀ i j, db i ^ r = db j ^ r)
    (hsc : ∀ m n : ℕ, (∀ i j, da i ^ m * db i ^ n = da j ^ m * db j ^ n) → r ∣ m ∧ r ∣ n)
    {G : Matrix (Fin 3) (Fin 3) K} (hrow : ∀ i, ∃ j, G i j ≠ 0)
    (hGa : ∀ i j, σ (da i) * G i j * da j = G i j)
    (hGb : ∀ i j, σ (db i) * G i j * db j = G i j)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : G i j = 0 := by
  by_contra hG
  have rel : ∀ x y, G x y ≠ 0 → σ (da x) * da y = 1 ∧ σ (db x) * db y = 1 :=
    fun x y hxy => ⟨u3f_rel hxy (hGa x y), u3f_rel hxy (hGb x y)⟩
  obtain ⟨h1a, h1b⟩ := rel i j hG
  obtain ⟨l, hl⟩ := hrow k
  obtain ⟨hla, hlb⟩ := rel k l hl
  have hne : ∀ {x y : Fin 3}, x ≠ y → da x ≠ da y ∨ db x ≠ db y :=
    fun hxy => u3f_char_ne hr hda hdb hra hrb hsc hxy
  rcases u3f_fin3_cases i j k l hij hik hjk with hl' | hl' | hl'
  · rw [hl'] at hla hlb
    rcases hne hjk with h | h
    · exact h (u3f_dual hσ hla h1a)
    · exact h (u3f_dual hσ hlb h1b)
  · rw [hl'] at hla hlb
    rcases hne hik with h | h
    · exact h (u3f_cancel hσ h1a hla)
    · exact h (u3f_cancel hσ h1b hlb)
  · rw [hl'] at hla hlb
    obtain ⟨m, n, hmn, hv⟩ := u3f_pigeon hr (hda k) (hdb k) (hra i k) (hrb i k)
    apply hmn
    apply hsc m n
    have hnorm : σ (da k ^ m * db k ^ n) * (da k ^ m * db k ^ n) = 1 := by
      rw [map_mul, map_pow, map_pow, mul_mul_mul_comm, ← mul_pow, ← mul_pow, hla, hlb]
      simp
    have hj : (da j ^ m * db j ^ n) * σ (da k ^ m * db k ^ n) = 1 := by
      rw [← hv, map_mul, map_pow, map_pow, mul_mul_mul_comm, ← mul_pow, ← mul_pow,
        mul_comm (da j), h1a, mul_comm (db j), h1b]
      simp
    have hjt := u3f_norm_aux _ _ hnorm hj
    have hall : ∀ x, da x ^ m * db x ^ n = da k ^ m * db k ^ n := by
      intro x
      rcases u3f_fin3_cases i j k x hij hik hjk with hx | hx | hx
      · rw [hx, hv]
      · rw [hx, hjt]
      · rw [hx]
    intro x y
    rw [hall x, hall y]

end Offdiag

section Matrices

variable {K : Type} [Field K]

theorem u3f_scalar_iff {M B : Matrix (Fin 3) (Fin 3) K} (hB : IsUnit B) {d : Fin 3 → K}
    (h : M * B = B * Matrix.diagonal d) (t : K) :
    M = t • (1 : Matrix (Fin 3) (Fin 3) K) ↔ ∀ i, d i = t := by
  have hcomm : B * (t • (1 : Matrix (Fin 3) (Fin 3) K)) =
      (t • (1 : Matrix (Fin 3) (Fin 3) K)) * B := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hdiag : Matrix.diagonal d = t • (1 : Matrix (Fin 3) (Fin 3) K) ↔ ∀ i, d i = t := by
    rw [Matrix.smul_one_eq_diagonal]
    constructor
    · intro hd i
      simpa using congrFun (congrFun hd i) i
    · intro hd
      exact congrArg Matrix.diagonal (funext hd)
  rw [← hdiag]
  constructor
  · intro hM
    rw [hM] at h
    exact hB.mul_right_inj.mp (h.symm.trans hcomm.symm)
  · intro hd
    rw [hd] at h
    exact hB.mul_left_inj.mp (h.trans hcomm)

end Matrices

section Gram

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3f_gram_eq {x B : Matrix (Fin 3) (Fin 3) K} (hx : (x.map h.bar)ᵀ * x = 1)
    {d : Fin 3 → K} (hxB : x * B = B * Matrix.diagonal d) (i j : Fin 3) :
    h.bar (d i) * ((B.map h.bar)ᵀ * B) i j * d j = ((B.map h.bar)ᵀ * B) i j := by
  have h1 := CFSG.ClassicalGroups.UnitaryFlag.conjTranspose_mul_mul h 1 x B
  have h2 := CFSG.ClassicalGroups.UnitaryFlag.conjTranspose_mul_mul h 1 B (Matrix.diagonal d)
  simp only [Matrix.mul_one] at h1 h2
  rw [hx, Matrix.mul_one, hxB] at h1
  have h3 := h2.symm.trans h1
  have hdm : ((Matrix.diagonal d).map h.bar)ᵀ = Matrix.diagonal (fun m => h.bar (d m)) := by
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
  rw [hdm] at h3
  have h4 := congrFun (congrFun h3 i) j
  rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at h4

theorem u3f_gram_row (B : GL (Fin 3) K) (i : Fin 3) :
    ∃ j, (((B : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      (B : Matrix (Fin 3) (Fin 3) K)) i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hdet := Matrix.det_eq_zero_of_row_eq_zero i hcon
  rw [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hB : (B : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := GeneralLinearGroup.det_ne_zero B
  have e : ((B : Matrix (Fin 3) (Fin 3) K).map h.bar).det =
      h.bar (B : Matrix (Fin 3) (Fin 3) K).det := (RingHom.map_det h.bar _).symm
  rw [e] at hdet
  exact mul_ne_zero ((map_ne_zero h.bar).mpr hB) hB hdet

theorem u3f_gram_herm (B : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    h.bar (((B.map h.bar)ᵀ * B) i j) = ((B.map h.bar)ᵀ * B) j i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    h.bar_bar]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem u3f_exists_scale (G : Matrix (Fin 3) (Fin 3) K) (hdiag : ∀ i j, i ≠ j → G i j = 0)
    (hrow : ∀ i, ∃ j, G i j ≠ 0) (hherm : ∀ i, h.bar (G i i) = G i i) :
    ∃ c : Fin 3 → K, (∀ i, c i ≠ 0) ∧
      ∀ i j, h.bar (c i) * G i j * c j = (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  have hGii : ∀ i, G i i ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    rcases eq_or_ne i j with hij | hij
    · subst hij; exact hj
    · exact absurd (hdiag i j hij) hj
  have hex : ∀ i, ∃ c : K, h.bar c * c = (G i i)⁻¹ := by
    intro i
    have : Fact p.Prime := ⟨h.prime⟩
    have := h.charP
    have := h.finite
    have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, pow_mul']
    have hfix : CFSG.LieType.BorelTits.unitaryInvolution K p f (G i i)⁻¹ = (G i i)⁻¹ := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply, map_inv₀, hherm]
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hfix
      (inv_ne_zero (hGii i))
    refine ⟨c, ?_⟩
    rw [h.bar_apply, ← CFSG.LieType.BorelTits.unitaryInvolution_apply K p f c]
    exact hc
  choose c hc using hex
  refine ⟨c, fun i hci => ?_, fun i j => ?_⟩
  · have := hc i
    rw [hci, map_zero, zero_mul] at this
    exact inv_ne_zero (hGii i) this.symm
  · rcases eq_or_ne i j with hij | hij
    · subst hij
      rw [Matrix.one_apply_eq, mul_right_comm, hc i, inv_mul_cancel₀ (hGii i)]
    · rw [Matrix.one_apply_ne hij, hdiag i j hij, mul_zero, zero_mul]

end Gram

section Main

variable {K : Type} [Field K]

theorem u3f_eig_pow {r : ℕ} {x B : GL (Fin 3) K} {d : Fin 3 → K} {u : Kˣ}
    (hx : (x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal d)
    (hxu : x ^ r = GeneralLinearGroup.scalar (Fin 3) u) (i : Fin 3) : d i ^ r = u := by
  have h1 := (u3f_scalar_iff B.isUnit (CFSG.GH74.GLS.Stage2.OddAut.mul_pow_diag hx r) (u : K)).mp
  have h2 : (x : Matrix (Fin 3) (Fin 3) K) ^ r = (u : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_pow_eq_pow_val, hxu, CFSG.GH74.GLS.Stage2.OddAut.coe_scalar_smul]
  exact h1 h2 i

theorem u3f_hsc {r : ℕ} {a b B : GL (Fin 3) K} {da db : Fin 3 → K}
    (hBa : (a : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal da)
    (hBb : (b : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal db)
    (hda0 : ∀ i, da i ≠ 0) (hdb0 : ∀ i, db i ≠ 0)
    (hind : ∀ m n : ℕ, (∃ w : Kˣ, a ^ m * b ^ n = GeneralLinearGroup.scalar (Fin 3) w) →
      r ∣ m ∧ r ∣ n) :
    ∀ m n : ℕ, (∀ i j, da i ^ m * db i ^ n = da j ^ m * db j ^ n) → r ∣ m ∧ r ∣ n := by
  intro m n hmn
  apply hind m n
  have hmat : ((a ^ m * b ^ n : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B =
      B * Matrix.diagonal (fun i => da i ^ m * db i ^ n) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Matrix.mul_assoc,
      CFSG.GH74.GLS.Stage2.OddAut.mul_pow_diag hBb n, ← Matrix.mul_assoc,
      CFSG.GH74.GLS.Stage2.OddAut.mul_pow_diag hBa m, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    rfl
  have ht : da 0 ^ m * db 0 ^ n ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (hda0 0)) (pow_ne_zero _ (hdb0 0))
  refine ⟨Units.mk0 _ ht, Units.ext ?_⟩
  rw [CFSG.GH74.GLS.Stage2.OddAut.coe_scalar_smul, Units.val_mk0]
  exact (u3f_scalar_iff B.isUnit hmat _).mpr (fun i => hmn i 0)

theorem u3f_eig_scale {x B : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K} (c : Fin 3 → K)
    (hxB : x * B = B * Matrix.diagonal d) :
    x * (B * Matrix.diagonal c) = (B * Matrix.diagonal c) * Matrix.diagonal d := by
  have hcomm : Matrix.diagonal d * Matrix.diagonal c = Matrix.diagonal c * Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
  rw [← Matrix.mul_assoc, hxB, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]

end Main

theorem u3_orthonormal_frame {p f r : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hr : r.Prime) (a b : GL (Fin 3) K)
    (ha : a ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hb : b ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (ua ub : Kˣ) (hau : a ^ r = GeneralLinearGroup.scalar (Fin 3) ua)
    (hbu : b ^ r = GeneralLinearGroup.scalar (Fin 3) ub)
    (hind : ∀ m n : ℕ, (∃ w : Kˣ, a ^ m * b ^ n = GeneralLinearGroup.scalar (Fin 3) w) →
      r ∣ m ∧ r ∣ n)
    (B : GL (Fin 3) K) (da db : Fin 3 → K)
    (hBa : (a : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal da)
    (hBb : (b : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal db) :
    ∃ (E : GL (Fin 3) K) (ea eb : Fin 3 → K),
      E ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
      (a : Matrix (Fin 3) (Fin 3) K) * (E : Matrix (Fin 3) (Fin 3) K) =
        (E : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal ea ∧
      (b : Matrix (Fin 3) (Fin 3) K) * (E : Matrix (Fin 3) (Fin 3) K) =
        (E : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal eb := by
  have hdapow := fun i => u3f_eig_pow hBa hau i
  have hdbpow := fun i => u3f_eig_pow hBb hbu i
  have hda0 : ∀ i, da i ≠ 0 := fun i h0 =>
    ua.ne_zero (by rw [← hdapow i, h0, zero_pow hr.ne_zero])
  have hdb0 : ∀ i, db i ≠ 0 := fun i h0 =>
    ub.ne_zero (by rw [← hdbpow i, h0, zero_pow hr.ne_zero])
  have hra : ∀ i j, da i ^ r = da j ^ r := fun i j => (hdapow i).trans (hdapow j).symm
  have hrb : ∀ i j, db i ^ r = db j ^ r := fun i j => (hdbpow i).trans (hdbpow j).symm
  have hsc := u3f_hsc hBa hBb hda0 hdb0 hind
  have hax : ((a : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (a : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := mem_primeFormUnitary.mp ha
    rwa [Units.val_one, Matrix.mul_one] at this
  have hbx : ((b : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (b : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := mem_primeFormUnitary.mp hb
    rwa [Units.val_one, Matrix.mul_one] at this
  have hrow := u3f_gram_row h B
  have hoff : ∀ i j, i ≠ j →
      (((B : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (B : Matrix (Fin 3) (Fin 3) K)) i j = 0 := by
    intro i j hij
    obtain ⟨k, hik, hjk⟩ := u3f_exists_third i j hij
    exact u3f_offdiag h.bar_bar hr hda0 hdb0 hra hrb hsc hrow (u3f_gram_eq h hax hBa)
      (u3f_gram_eq h hbx hBb) hij hik hjk
  obtain ⟨c, hc0, hc⟩ := u3f_exists_scale h _ hoff hrow fun i => u3f_gram_herm h _ i i
  have hEdet : ((B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero B)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i)
  have hE : ((GeneralLinearGroup.mkOfDetNeZero _ hEdet : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal c := rfl
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hEdet, da, db, ?_, ?_, ?_⟩
  · rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hE]
    have h1 := CFSG.ClassicalGroups.UnitaryFlag.conjTranspose_mul_mul h 1
      (B : Matrix (Fin 3) (Fin 3) K) (Matrix.diagonal c)
    simp only [Matrix.mul_one] at h1
    rw [h1]
    ext i j
    have hdm : ((Matrix.diagonal c).map h.bar)ᵀ = Matrix.diagonal (fun m => h.bar (c m)) := by
      rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose]
    rw [hdm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact hc i j
  · rw [hE]
    exact u3f_eig_scale c hBa
  · rw [hE]
    exact u3f_eig_scale c hBb

end CFSG.GH74.GLS.Stage2.Bender.Thm1
