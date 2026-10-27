module

public import CFSG.GH74.GLS.Stage2.OddAut.HeisPair
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut

section Central

variable {K : Type} [Field K]

theorem u3_xi_rel {ξ m0 : K} (hξ3 : ξ ^ 3 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0) :
    ∀ i j : Fin 3, ξ ^ (i : ℕ) * m0 = ξ * (ξ ^ (j : ℕ) * m0) → i = j + 1 := by
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  intro i j h
  have h' : ξ ^ (i : ℕ) = ξ ^ ((j : ℕ) + 1) := by
    apply mul_right_cancel₀ hm0
    rw [pow_succ']
    linear_combination h
  fin_cases i <;> fin_cases j <;> simp at h' ⊢
  all_goals (apply hξ1; first
    | exact h'.symm
    | exact h'.trans hξ3
    | linear_combination ξ * h' + hξ3
    | linear_combination (1 - ξ) * hξ3 - ξ * h'
    | exact (mul_left_cancel₀ hξ0 (by linear_combination h' : ξ * 1 = ξ * ξ)).symm
    | exact (mul_left_cancel₀ hξ0 (by linear_combination -h' : ξ * 1 = ξ * ξ)).symm)

theorem u3_xi_inj {ξ m0 : K} (hξ3 : ξ ^ 3 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0) :
    ∀ i j : Fin 3, ξ ^ (i : ℕ) * m0 = ξ ^ (j : ℕ) * m0 → i = j := by
  intro i j h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ξ = 3 := orderOf_eq_prime hξ3 hξ1
  have h1 : ξ ^ (i : ℕ) = ξ ^ (j : ℕ) := mul_right_cancel₀ hm0 h
  exact Fin.ext (pow_injOn_Iio_orderOf (x := ξ) (by rw [hord]; exact i.2)
    (by rw [hord]; exact j.2) h1)

theorem u3_scalar_of_comm_heis {ξ m0 : K} (hξ3 : ξ ^ 3 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0)
    {x y A B : GL (Fin 3) K}
    (hxB : (x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
      (B : Matrix (Fin 3) (Fin 3) K) * Matrix.diagonal (fun i : Fin 3 => ξ ^ (i : ℕ) * m0))
    (hxy : (x : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
      ξ • ((y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)))
    (hAx : (A : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) =
      (x : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K))
    (hAy : (A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
      (y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) :
    ∃ w : Kˣ, A = GeneralLinearGroup.scalar (Fin 3) w := by
  classical
  set Δ : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal (fun i : Fin 3 => ξ ^ (i : ℕ) * m0)
    with hΔ
  set Bi : Matrix (Fin 3) (Fin 3) K := ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hBi
  have hBBi : (B : Matrix (Fin 3) (Fin 3) K) * Bi = 1 := by
    rw [hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : Bi * (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set A' : Matrix (Fin 3) (Fin 3) K := Bi * (A : Matrix (Fin 3) (Fin 3) K) * B with hA'
  set y' : Matrix (Fin 3) (Fin 3) K := Bi * (y : Matrix (Fin 3) (Fin 3) K) * B with hy'
  have hBix : Bi * (x : Matrix (Fin 3) (Fin 3) K) = Δ * Bi := by
    calc Bi * (x : Matrix (Fin 3) (Fin 3) K)
        = Bi * (x : Matrix (Fin 3) (Fin 3) K) * ((B : Matrix (Fin 3) (Fin 3) K) * Bi) := by
          rw [hBBi, Matrix.mul_one]
      _ = Bi * ((x : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K)) * Bi := by
          simp only [Matrix.mul_assoc]
      _ = Bi * ((B : Matrix (Fin 3) (Fin 3) K) * Δ) * Bi := by rw [hxB]
      _ = Δ * Bi := by
          simp only [← Matrix.mul_assoc]
          rw [hBiB, Matrix.one_mul]
  have hA'Δ : A' * Δ = Δ * A' := by
    calc A' * Δ = Bi * (A : Matrix (Fin 3) (Fin 3) K) * ((B : Matrix (Fin 3) (Fin 3) K) * Δ) := by
          simp only [hA', Matrix.mul_assoc]
      _ = Bi * (A : Matrix (Fin 3) (Fin 3) K) * ((x : Matrix (Fin 3) (Fin 3) K) *
            (B : Matrix (Fin 3) (Fin 3) K)) := by rw [← hxB]
      _ = Bi * ((A : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) *
            (B : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
      _ = Bi * ((x : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) *
            (B : Matrix (Fin 3) (Fin 3) K) := by rw [hAx]
      _ = (Bi * (x : Matrix (Fin 3) (Fin 3) K)) * (A : Matrix (Fin 3) (Fin 3) K) *
            (B : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
      _ = Δ * A' := by rw [hBix]; simp only [hA', Matrix.mul_assoc]
  have hy'Δ : Δ * y' = ξ • (y' * Δ) := by
    calc Δ * y' = (Δ * Bi) * (y : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) := by
          simp only [hy', Matrix.mul_assoc]
      _ = (Bi * (x : Matrix (Fin 3) (Fin 3) K)) * (y : Matrix (Fin 3) (Fin 3) K) *
            (B : Matrix (Fin 3) (Fin 3) K) := by rw [hBix]
      _ = Bi * ((x : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)) *
            (B : Matrix (Fin 3) (Fin 3) K) := by simp only [Matrix.mul_assoc]
      _ = ξ • (Bi * ((y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) *
            (B : Matrix (Fin 3) (Fin 3) K)) := by
          rw [hxy, Matrix.mul_smul, Matrix.smul_mul]
      _ = ξ • (y' * Δ) := by
          congr 1
          calc Bi * ((y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) *
                (B : Matrix (Fin 3) (Fin 3) K)
              = Bi * (y : Matrix (Fin 3) (Fin 3) K) * ((x : Matrix (Fin 3) (Fin 3) K) *
                  (B : Matrix (Fin 3) (Fin 3) K)) := by simp only [Matrix.mul_assoc]
            _ = Bi * (y : Matrix (Fin 3) (Fin 3) K) * ((B : Matrix (Fin 3) (Fin 3) K) * Δ) := by
                rw [hxB]
            _ = y' * Δ := by simp only [hy', Matrix.mul_assoc]
  have hA'y' : A' * y' = y' * A' := by
    calc A' * y' = Bi * (A : Matrix (Fin 3) (Fin 3) K) *
          ((B : Matrix (Fin 3) (Fin 3) K) * Bi) * (y : Matrix (Fin 3) (Fin 3) K) *
            (B : Matrix (Fin 3) (Fin 3) K) := by simp only [hA', hy', Matrix.mul_assoc]
      _ = Bi * ((A : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K)) *
            (B : Matrix (Fin 3) (Fin 3) K) := by
          rw [hBBi]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Bi * ((y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) *
            (B : Matrix (Fin 3) (Fin 3) K) := by rw [hAy]
      _ = y' * A' := by
          have : Bi * ((y : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K)) *
              (B : Matrix (Fin 3) (Fin 3) K) = Bi * (y : Matrix (Fin 3) (Fin 3) K) *
                ((B : Matrix (Fin 3) (Fin 3) K) * Bi) * (A : Matrix (Fin 3) (Fin 3) K) *
                  (B : Matrix (Fin 3) (Fin 3) K) := by
            rw [hBBi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
          rw [this]
          simp only [hA', hy', Matrix.mul_assoc]
  have hmne : ∀ i j : Fin 3, i ≠ j → ξ ^ (j : ℕ) * m0 ≠ ξ ^ (i : ℕ) * m0 := fun i j hij h =>
    hij (u3_xi_inj hξ3 hξ1 hm0 j i h).symm
  have hoff : ∀ i j : Fin 3, i ≠ j → A' i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hA'Δ i) j
    rw [hΔ, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    by_contra hne
    apply hmne i j hij
    exact mul_left_cancel₀ hne (by linear_combination e)
  have hyij : ∀ i j : Fin 3, y' i j ≠ 0 → i = j + 1 := by
    intro i j hne
    have e := congrFun (congrFun hy'Δ i) j
    rw [hΔ, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul] at e
    apply u3_xi_rel hξ3 hξ1 hm0 i j
    exact mul_right_cancel₀ hne (by linear_combination e)
  have hy'U : y' = ((B⁻¹ * y * B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hy', hBi, Units.val_mul, Units.val_mul]
  have hy'det : y'.det ≠ 0 := by
    rw [hy'U]
    exact GeneralLinearGroup.det_ne_zero _
  have hcol : ∀ j : Fin 3, ∃ i, y' i j ≠ 0 := by
    intro j
    by_contra hcon
    push Not at hcon
    exact hy'det (Matrix.det_eq_zero_of_column_eq_zero j hcon)
  have hdiag : ∀ j : Fin 3, A' (j + 1) (j + 1) = A' j j := by
    intro j
    obtain ⟨i, hi⟩ := hcol j
    have hij := hyij i j hi
    subst hij
    have e := congrFun (congrFun hA'y' (j + 1)) j
    have e1 : (A' * y') (j + 1) j = A' (j + 1) (j + 1) * y' (j + 1) j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (j + 1)]
      · intro k _ hk
        rw [hoff (j + 1) k (Ne.symm hk), zero_mul]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    have e2 : (y' * A') (j + 1) j = y' (j + 1) j * A' j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro k _ hk
        rw [hoff k j hk, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    rw [e1, e2] at e
    exact mul_right_cancel₀ hi (by linear_combination e)
  have h10 : A' 1 1 = A' 0 0 := hdiag 0
  have h21 : A' 2 2 = A' 1 1 := hdiag 1
  have hA'scal : A' = (A' 0 0) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      fin_cases a <;> simp [h10, h21]
    · rw [hoff a b hab, Matrix.smul_apply, Matrix.one_apply_ne hab, smul_zero]
  have hAeq : (A : Matrix (Fin 3) (Fin 3) K) = (A' 0 0) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    calc (A : Matrix (Fin 3) (Fin 3) K) = ((B : Matrix (Fin 3) (Fin 3) K) * Bi) *
          (A : Matrix (Fin 3) (Fin 3) K) * ((B : Matrix (Fin 3) (Fin 3) K) * Bi) := by
          rw [hBBi, Matrix.one_mul, Matrix.mul_one]
      _ = (B : Matrix (Fin 3) (Fin 3) K) * A' * Bi := by simp only [hA', Matrix.mul_assoc]
      _ = (A' 0 0) • (1 : Matrix (Fin 3) (Fin 3) K) := by
          rw [hA'scal]
          simp [hBBi]
  have hα : A' 0 0 ≠ 0 := by
    intro h0
    have hdet := GeneralLinearGroup.det_ne_zero A
    rw [hAeq, h0, zero_smul, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 (A' 0 0) hα, Units.ext ?_⟩
  rw [coe_scalar_smul, Units.val_mk0]
  exact hAeq

end Central

section InterD

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_comm_of_coprime (A w : U3U h) {N : ℕ} (hN : Nat.Coprime N 3)
    (hAN : ∃ w₀ : Kˣ, (A : GL (Fin 3) K) ^ N = GeneralLinearGroup.scalar (Fin 3) w₀)
    (hw3 : ∃ w₁ : Kˣ, (w : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) w₁)
    (hc : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A *
        primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) w =
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) w *
        primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A) :
    (A : GL (Fin 3) K) * w = w * A := by
  obtain ⟨l, hl⟩ := (u3_conj_eq_one_iff h (A * w * A⁻¹ * w⁻¹)).1 (by
    simp only [map_mul, map_inv]
    rw [hc]
    group)
  have hAw : (A : GL (Fin 3) K) * w =
      GeneralLinearGroup.scalar (Fin 3) l * ((w : GL (Fin 3) K) * A) := by
    have hl' : (A : GL (Fin 3) K) * w * (A : GL (Fin 3) K)⁻¹ * (w : GL (Fin 3) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) l := by simpa using hl
    calc (A : GL (Fin 3) K) * w = ((A : GL (Fin 3) K) * w * (A : GL (Fin 3) K)⁻¹ *
          (w : GL (Fin 3) K)⁻¹) * ((w : GL (Fin 3) K) * A) := by group
      _ = _ := by rw [hl']
  have hcent : ∀ (c : Kˣ) (g : GL (Fin 3) K), Commute g (GeneralLinearGroup.scalar (Fin 3) c) :=
    fun c g => (scalar_commute c g).symm
  obtain ⟨w₀, hw₀⟩ := hAN
  obtain ⟨w₁, hw₁⟩ := hw3
  have hlN : l ^ N = 1 := by
    have h1 := pow_mul_pow_comm_central (fun g => hcent l g) hAw N 1
    rw [pow_one, mul_one, hw₀] at h1
    have h2 : GeneralLinearGroup.scalar (Fin 3) w₀ * (w : GL (Fin 3) K) =
        (w : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) w₀ :=
      ((hcent w₀ (w : GL (Fin 3) K)).eq).symm
    have h3 : GeneralLinearGroup.scalar (Fin 3) (l ^ N) *
        ((w : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) w₀) =
          1 * ((w : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) w₀) := by
      rw [map_pow, one_mul, ← h1, h2]
    exact scalar_injective (by rw [map_one]; exact mul_right_cancel h3)
  have hl3 : l ^ 3 = 1 := by
    have h1 := pow_mul_pow_comm_central (fun g => hcent l g) hAw 1 3
    rw [pow_one, one_mul, hw₁] at h1
    have h2 : (A : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) w₁ =
        GeneralLinearGroup.scalar (Fin 3) w₁ * (A : GL (Fin 3) K) :=
      (hcent w₁ (A : GL (Fin 3) K)).eq
    have h3 : GeneralLinearGroup.scalar (Fin 3) (l ^ 3) *
        (GeneralLinearGroup.scalar (Fin 3) w₁ * (A : GL (Fin 3) K)) =
          1 * (GeneralLinearGroup.scalar (Fin 3) w₁ * (A : GL (Fin 3) K)) := by
      rw [map_pow, one_mul, ← h1, h2]
    exact scalar_injective (by rw [map_one]; exact mul_right_cancel h3)
  have hl1 : l = 1 := by
    have := Nat.eq_one_of_dvd_coprimes hN (orderOf_dvd_of_pow_eq_one hlN)
      (orderOf_dvd_of_pow_eq_one hl3)
    exact orderOf_eq_one_iff.mp this
  rw [hAw, hl1, map_one, one_mul]

theorem u3_heis_inter_D {V Z : Subgroup (MulAut (U3T h))} (hZc : Nat.Coprime (Nat.card Z) 3)
    (hcomm : ∀ v ∈ V, ∀ z ∈ Z, v * z = z * v) (hVe : ∀ v ∈ V, v ^ 3 = 1)
    {x y E : U3U h} {ξ m0 : K} (hξ3 : ξ ^ 3 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0)
    (hx : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∈ V)
    (hy : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) y ∈ V)
    (hxE : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((E : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          Matrix.diagonal (fun i : Fin 3 => ξ ^ (i : ℕ) * m0))
    (hxy : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((y : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ξ • (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) :
    ∀ z ∈ Z, z ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → z = 1 := by
  intro z hz hzD
  obtain ⟨A, rfl⟩ := hzD
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hc
  have hzN : (c A) ^ Nat.card Z = 1 := by
    have h' : (⟨c A, hz⟩ : ↥Z) ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h'
  have hAN : ∃ w₀ : Kˣ, (A : GL (Fin 3) K) ^ Nat.card Z =
      GeneralLinearGroup.scalar (Fin 3) w₀ := by
    obtain ⟨w₀, hw₀⟩ := (u3_conj_eq_one_iff h (A ^ Nat.card Z)).1 (by rw [map_pow]; exact hzN)
    exact ⟨w₀, by simpa using hw₀⟩
  have hcube : ∀ w : U3U h, c w ∈ V → ∃ w₁ : Kˣ, (w : GL (Fin 3) K) ^ 3 =
      GeneralLinearGroup.scalar (Fin 3) w₁ := by
    intro w hw
    obtain ⟨w₁, hw₁⟩ := (u3_conj_eq_one_iff h (w ^ 3)).1 (by rw [map_pow]; exact hVe _ hw)
    exact ⟨w₁, by simpa using hw₁⟩
  have hAx := u3_comm_of_coprime h A x hZc hAN (hcube x hx) (hcomm _ hx _ hz).symm
  have hAy := u3_comm_of_coprime h A y hZc hAN (hcube y hy) (hcomm _ hy _ hz).symm
  have hAxm : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hAx]
  have hAym : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hAy]
  obtain ⟨w, hw⟩ := u3_scalar_of_comm_heis hξ3 hξ1 hm0 (x := (x : GL (Fin 3) K))
    (y := (y : GL (Fin 3) K)) (A := (A : GL (Fin 3) K)) (B := (E : GL (Fin 3) K)) hxE hxy hAxm
    hAym
  exact (u3_conj_eq_one_iff h A).2 ⟨w, hw⟩

end InterD

end CFSG.GH74.GLS.Stage2.Bender.Thm1
