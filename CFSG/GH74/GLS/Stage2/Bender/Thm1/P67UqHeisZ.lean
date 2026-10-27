module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqBase
import CFSG.GH74.GLS.Stage2.OddAut.HeisPair
import CFSG.GH74.GLS.Stage2.OddAut.LinNAut

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut

variable {K : Type} [Field K]

theorem uq5_xi_inj {ξ m0 : K} (hξ5 : ξ ^ 5 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0) :
    ∀ i j : Fin 5, ξ ^ (i : ℕ) * m0 = ξ ^ (j : ℕ) * m0 → i = j := by
  intro i j h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf ξ = 5 := orderOf_eq_prime hξ5 hξ1
  have h1 : ξ ^ (i : ℕ) = ξ ^ (j : ℕ) := mul_right_cancel₀ hm0 h
  exact Fin.ext (pow_injOn_Iio_orderOf (x := ξ) (by rw [hord]; exact i.2)
    (by rw [hord]; exact j.2) h1)

theorem uq5_xi_rel {ξ m0 : K} (hξ5 : ξ ^ 5 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0) :
    ∀ i j : Fin 5, ξ ^ (i : ℕ) * m0 = ξ * (ξ ^ (j : ℕ) * m0) → i = j + 1 := by
  intro i j h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf ξ = 5 := orderOf_eq_prime hξ5 hξ1
  have h' : ξ ^ (i : ℕ) = ξ ^ ((j : ℕ) + 1) := by
    apply mul_right_cancel₀ hm0
    rw [pow_succ']
    linear_combination h
  have h'' : ξ ^ ((j : ℕ) + 1) = ξ ^ (((j : ℕ) + 1) % 5) := by
    conv_lhs => rw [← Nat.mod_add_div ((j : ℕ) + 1) 5, pow_add, pow_mul, hξ5, one_pow, mul_one]
  have hi : (i : ℕ) = ((j : ℕ) + 1) % 5 :=
    pow_injOn_Iio_orderOf (x := ξ) (by rw [hord]; exact i.2)
      (by rw [hord]; exact Nat.mod_lt _ (by norm_num)) (h'.trans h'')
  apply Fin.ext
  rw [hi, Fin.val_add, Fin.val_one]

theorem uq5_scalar_of_comm_heis {ξ m0 : K} (hξ5 : ξ ^ 5 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0)
    {x y A B : GL (Fin 5) K}
    (hxB : (x : Matrix (Fin 5) (Fin 5) K) * (B : Matrix (Fin 5) (Fin 5) K) =
      (B : Matrix (Fin 5) (Fin 5) K) * Matrix.diagonal (fun i : Fin 5 => ξ ^ (i : ℕ) * m0))
    (hxy : (x : Matrix (Fin 5) (Fin 5) K) * (y : Matrix (Fin 5) (Fin 5) K) =
      ξ • ((y : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K)))
    (hAx : (A : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K) =
      (x : Matrix (Fin 5) (Fin 5) K) * (A : Matrix (Fin 5) (Fin 5) K))
    (hAy : (A : Matrix (Fin 5) (Fin 5) K) * (y : Matrix (Fin 5) (Fin 5) K) =
      (y : Matrix (Fin 5) (Fin 5) K) * (A : Matrix (Fin 5) (Fin 5) K)) :
    ∃ w : Kˣ, A = GeneralLinearGroup.scalar (Fin 5) w := by
  classical
  set Δ : Matrix (Fin 5) (Fin 5) K := Matrix.diagonal (fun i : Fin 5 => ξ ^ (i : ℕ) * m0)
    with hΔ
  set Bi : Matrix (Fin 5) (Fin 5) K := ((B⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    with hBi
  have hBBi : (B : Matrix (Fin 5) (Fin 5) K) * Bi = 1 := by
    rw [hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : Bi * (B : Matrix (Fin 5) (Fin 5) K) = 1 := by
    rw [hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set A' : Matrix (Fin 5) (Fin 5) K := Bi * (A : Matrix (Fin 5) (Fin 5) K) * B with hA'
  set y' : Matrix (Fin 5) (Fin 5) K := Bi * (y : Matrix (Fin 5) (Fin 5) K) * B with hy'
  have hBix : Bi * (x : Matrix (Fin 5) (Fin 5) K) = Δ * Bi := by
    calc Bi * (x : Matrix (Fin 5) (Fin 5) K)
        = Bi * (x : Matrix (Fin 5) (Fin 5) K) * ((B : Matrix (Fin 5) (Fin 5) K) * Bi) := by
          rw [hBBi, Matrix.mul_one]
      _ = Bi * ((x : Matrix (Fin 5) (Fin 5) K) * (B : Matrix (Fin 5) (Fin 5) K)) * Bi := by
          simp only [Matrix.mul_assoc]
      _ = Bi * ((B : Matrix (Fin 5) (Fin 5) K) * Δ) * Bi := by rw [hxB]
      _ = Δ * Bi := by
          simp only [← Matrix.mul_assoc]
          rw [hBiB, Matrix.one_mul]
  have hA'Δ : A' * Δ = Δ * A' := by
    calc A' * Δ = Bi * (A : Matrix (Fin 5) (Fin 5) K) * ((B : Matrix (Fin 5) (Fin 5) K) * Δ) := by
          simp only [hA', Matrix.mul_assoc]
      _ = Bi * (A : Matrix (Fin 5) (Fin 5) K) * ((x : Matrix (Fin 5) (Fin 5) K) *
            (B : Matrix (Fin 5) (Fin 5) K)) := by rw [← hxB]
      _ = Bi * ((A : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K)) *
            (B : Matrix (Fin 5) (Fin 5) K) := by simp only [Matrix.mul_assoc]
      _ = Bi * ((x : Matrix (Fin 5) (Fin 5) K) * (A : Matrix (Fin 5) (Fin 5) K)) *
            (B : Matrix (Fin 5) (Fin 5) K) := by rw [hAx]
      _ = (Bi * (x : Matrix (Fin 5) (Fin 5) K)) * (A : Matrix (Fin 5) (Fin 5) K) *
            (B : Matrix (Fin 5) (Fin 5) K) := by simp only [Matrix.mul_assoc]
      _ = Δ * A' := by rw [hBix]; simp only [hA', Matrix.mul_assoc]
  have hy'Δ : Δ * y' = ξ • (y' * Δ) := by
    calc Δ * y' = (Δ * Bi) * (y : Matrix (Fin 5) (Fin 5) K) * (B : Matrix (Fin 5) (Fin 5) K) := by
          simp only [hy', Matrix.mul_assoc]
      _ = (Bi * (x : Matrix (Fin 5) (Fin 5) K)) * (y : Matrix (Fin 5) (Fin 5) K) *
            (B : Matrix (Fin 5) (Fin 5) K) := by rw [hBix]
      _ = Bi * ((x : Matrix (Fin 5) (Fin 5) K) * (y : Matrix (Fin 5) (Fin 5) K)) *
            (B : Matrix (Fin 5) (Fin 5) K) := by simp only [Matrix.mul_assoc]
      _ = ξ • (Bi * ((y : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K)) *
            (B : Matrix (Fin 5) (Fin 5) K)) := by
          rw [hxy, Matrix.mul_smul, Matrix.smul_mul]
      _ = ξ • (y' * Δ) := by
          congr 1
          calc Bi * ((y : Matrix (Fin 5) (Fin 5) K) * (x : Matrix (Fin 5) (Fin 5) K)) *
                (B : Matrix (Fin 5) (Fin 5) K)
              = Bi * (y : Matrix (Fin 5) (Fin 5) K) * ((x : Matrix (Fin 5) (Fin 5) K) *
                  (B : Matrix (Fin 5) (Fin 5) K)) := by simp only [Matrix.mul_assoc]
            _ = Bi * (y : Matrix (Fin 5) (Fin 5) K) * ((B : Matrix (Fin 5) (Fin 5) K) * Δ) := by
                rw [hxB]
            _ = y' * Δ := by simp only [hy', Matrix.mul_assoc]
  have hA'y' : A' * y' = y' * A' := by
    calc A' * y' = Bi * (A : Matrix (Fin 5) (Fin 5) K) *
          ((B : Matrix (Fin 5) (Fin 5) K) * Bi) * (y : Matrix (Fin 5) (Fin 5) K) *
            (B : Matrix (Fin 5) (Fin 5) K) := by simp only [hA', hy', Matrix.mul_assoc]
      _ = Bi * ((A : Matrix (Fin 5) (Fin 5) K) * (y : Matrix (Fin 5) (Fin 5) K)) *
            (B : Matrix (Fin 5) (Fin 5) K) := by
          rw [hBBi]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Bi * ((y : Matrix (Fin 5) (Fin 5) K) * (A : Matrix (Fin 5) (Fin 5) K)) *
            (B : Matrix (Fin 5) (Fin 5) K) := by rw [hAy]
      _ = y' * A' := by
          have : Bi * ((y : Matrix (Fin 5) (Fin 5) K) * (A : Matrix (Fin 5) (Fin 5) K)) *
              (B : Matrix (Fin 5) (Fin 5) K) = Bi * (y : Matrix (Fin 5) (Fin 5) K) *
                ((B : Matrix (Fin 5) (Fin 5) K) * Bi) * (A : Matrix (Fin 5) (Fin 5) K) *
                  (B : Matrix (Fin 5) (Fin 5) K) := by
            rw [hBBi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
          rw [this]
          simp only [hA', hy', Matrix.mul_assoc]
  have hmne : ∀ i j : Fin 5, i ≠ j → ξ ^ (j : ℕ) * m0 ≠ ξ ^ (i : ℕ) * m0 := fun i j hij h =>
    hij (uq5_xi_inj hξ5 hξ1 hm0 j i h).symm
  have hoff : ∀ i j : Fin 5, i ≠ j → A' i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hA'Δ i) j
    rw [hΔ, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    by_contra hne
    apply hmne i j hij
    exact mul_left_cancel₀ hne (by linear_combination e)
  have hyij : ∀ i j : Fin 5, y' i j ≠ 0 → i = j + 1 := by
    intro i j hne
    have e := congrFun (congrFun hy'Δ i) j
    rw [hΔ, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul] at e
    apply uq5_xi_rel hξ5 hξ1 hm0 i j
    exact mul_right_cancel₀ hne (by linear_combination e)
  have hy'U : y' = ((B⁻¹ * y * B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [hy', hBi, Units.val_mul, Units.val_mul]
  have hy'det : y'.det ≠ 0 := by
    rw [hy'U]
    exact GeneralLinearGroup.det_ne_zero _
  have hcol : ∀ j : Fin 5, ∃ i, y' i j ≠ 0 := by
    intro j
    by_contra hcon
    push Not at hcon
    exact hy'det (Matrix.det_eq_zero_of_column_eq_zero j hcon)
  have hdiag : ∀ j : Fin 5, A' (j + 1) (j + 1) = A' j j := by
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
  have h32 : A' 3 3 = A' 2 2 := hdiag 2
  have h43 : A' 4 4 = A' 3 3 := hdiag 3
  have hA'scal : A' = (A' 0 0) • (1 : Matrix (Fin 5) (Fin 5) K) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      fin_cases a <;> simp [h10, h21, h32, h43]
    · rw [hoff a b hab, Matrix.smul_apply, Matrix.one_apply_ne hab, smul_zero]
  have hAeq : (A : Matrix (Fin 5) (Fin 5) K) = (A' 0 0) • (1 : Matrix (Fin 5) (Fin 5) K) := by
    calc (A : Matrix (Fin 5) (Fin 5) K) = ((B : Matrix (Fin 5) (Fin 5) K) * Bi) *
          (A : Matrix (Fin 5) (Fin 5) K) * ((B : Matrix (Fin 5) (Fin 5) K) * Bi) := by
          rw [hBBi, Matrix.one_mul, Matrix.mul_one]
      _ = (B : Matrix (Fin 5) (Fin 5) K) * A' * Bi := by simp only [hA', Matrix.mul_assoc]
      _ = (A' 0 0) • (1 : Matrix (Fin 5) (Fin 5) K) := by
          rw [hA'scal]
          simp [hBBi]
  have hα : A' 0 0 ≠ 0 := by
    intro h0
    have hdet := GeneralLinearGroup.det_ne_zero A
    rw [hAeq, h0, zero_smul, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 (A' 0 0) hα, Units.ext ?_⟩
  rw [coe_scalar_smul_n, Units.val_mk0]
  exact hAeq



theorem uq5_comm_of_coprime {p f : ℕ} (h : UnitaryFieldData p f K) (A w : UqU h 5) {N : ℕ}
    (hN : Nat.Coprime N 5)
    (hAN : ∃ w₀ : Kˣ, (A : GL (Fin 5) K) ^ N = GeneralLinearGroup.scalar (Fin 5) w₀)
    (hw5 : ∃ w₁ : Kˣ, (w : GL (Fin 5) K) ^ 5 = GeneralLinearGroup.scalar (Fin 5) w₁)
    (hc : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) A *
        primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) w =
      primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) w *
        primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) A) :
    (A : GL (Fin 5) K) * w = w * A := by
  obtain ⟨l, hl⟩ := (uq_conj_eq_one_iff h (by norm_num : 3 ≤ 5) (A * w * A⁻¹ * w⁻¹)).1 (by
    simp only [map_mul, map_inv]
    rw [hc]
    group)
  have hAw : (A : GL (Fin 5) K) * w =
      GeneralLinearGroup.scalar (Fin 5) l * ((w : GL (Fin 5) K) * A) := by
    have hl' : (A : GL (Fin 5) K) * w * (A : GL (Fin 5) K)⁻¹ * (w : GL (Fin 5) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 5) l := by simpa using hl
    calc (A : GL (Fin 5) K) * w = ((A : GL (Fin 5) K) * w * (A : GL (Fin 5) K)⁻¹ *
          (w : GL (Fin 5) K)⁻¹) * ((w : GL (Fin 5) K) * A) := by group
      _ = _ := by rw [hl']
  have hcent : ∀ (c : Kˣ) (g : GL (Fin 5) K), Commute g (GeneralLinearGroup.scalar (Fin 5) c) :=
    fun c g => (scalar_commute_n c g).symm
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin 5) : Kˣ →* GL (Fin 5) K) :=
    scalar_injective_n (by norm_num)
  obtain ⟨w₀, hw₀⟩ := hAN
  obtain ⟨w₁, hw₁⟩ := hw5
  have hlN : l ^ N = 1 := by
    have h1 := pow_mul_pow_comm_central (fun g => hcent l g) hAw N 1
    rw [pow_one, mul_one, hw₀] at h1
    have h2 : GeneralLinearGroup.scalar (Fin 5) w₀ * (w : GL (Fin 5) K) =
        (w : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) w₀ :=
      ((hcent w₀ (w : GL (Fin 5) K)).eq).symm
    have h3 : GeneralLinearGroup.scalar (Fin 5) (l ^ N) *
        ((w : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) w₀) =
          1 * ((w : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) w₀) := by
      rw [map_pow, one_mul, ← h1, h2]
    exact hinj (by rw [map_one]; exact mul_right_cancel h3)
  have hl5 : l ^ 5 = 1 := by
    have h1 := pow_mul_pow_comm_central (fun g => hcent l g) hAw 1 5
    rw [pow_one, one_mul, hw₁] at h1
    have h2 : (A : GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) w₁ =
        GeneralLinearGroup.scalar (Fin 5) w₁ * (A : GL (Fin 5) K) :=
      (hcent w₁ (A : GL (Fin 5) K)).eq
    have h3 : GeneralLinearGroup.scalar (Fin 5) (l ^ 5) *
        (GeneralLinearGroup.scalar (Fin 5) w₁ * (A : GL (Fin 5) K)) =
          1 * (GeneralLinearGroup.scalar (Fin 5) w₁ * (A : GL (Fin 5) K)) := by
      rw [map_pow, one_mul, ← h1, h2]
    exact hinj (by rw [map_one]; exact mul_right_cancel h3)
  rw [hAw, units_eq_one_of_coprime hN hlN hl5, map_one, one_mul]

theorem uq5_heis_inter_D {p f : ℕ} (h : UnitaryFieldData p f K)
    {V Z : Subgroup (MulAut (UqT h 5))} (hZc : Nat.Coprime (Nat.card Z) 5)
    (hcomm : ∀ v ∈ V, ∀ z ∈ Z, v * z = z * v) (hVe : ∀ v ∈ V, v ^ 5 = 1)
    {x y E : UqU h 5} {ξ m0 : K} (hξ5 : ξ ^ 5 = 1) (hξ1 : ξ ≠ 1) (hm0 : m0 ≠ 0)
    (hx : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) x ∈ V)
    (hy : primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) y ∈ V)
    (hxE : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((E : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((E : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          Matrix.diagonal (fun i : Fin 5 => ξ ^ (i : ℕ) * m0))
    (hxy : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ξ • (((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))) :
    ∀ z ∈ Z, z ∈ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) → z = 1 := by
  intro z hz hzD
  obtain ⟨A, rfl⟩ := hzD
  set c := primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hc
  have hzN : (c A) ^ Nat.card Z = 1 := by
    have h' : (⟨c A, hz⟩ : ↥Z) ^ Nat.card ↥Z = 1 := pow_card_eq_one'
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val h'
  have hAN : ∃ w₀ : Kˣ, (A : GL (Fin 5) K) ^ Nat.card Z =
      GeneralLinearGroup.scalar (Fin 5) w₀ := by
    obtain ⟨w₀, hw₀⟩ := (uq_conj_eq_one_iff h (by norm_num : 3 ≤ 5) (A ^ Nat.card Z)).1
      (by rw [map_pow]; exact hzN)
    exact ⟨w₀, by simpa using hw₀⟩
  have hfifth : ∀ w : UqU h 5, c w ∈ V → ∃ w₁ : Kˣ, (w : GL (Fin 5) K) ^ 5 =
      GeneralLinearGroup.scalar (Fin 5) w₁ := by
    intro w hw
    obtain ⟨w₁, hw₁⟩ := (uq_conj_eq_one_iff h (by norm_num : 3 ≤ 5) (w ^ 5)).1
      (by rw [map_pow]; exact hVe _ hw)
    exact ⟨w₁, by simpa using hw₁⟩
  have hAx := uq5_comm_of_coprime h A x hZc hAN (hfifth x hx) (hcomm _ hx _ hz).symm
  have hAy := uq5_comm_of_coprime h A y hZc hAN (hfifth y hy) (hcomm _ hy _ hz).symm
  have hAxm : ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hAx]
  have hAym : ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hAy]
  obtain ⟨w, hw⟩ := uq5_scalar_of_comm_heis hξ5 hξ1 hm0 (x := (x : GL (Fin 5) K))
    (y := (y : GL (Fin 5) K)) (A := (A : GL (Fin 5) K)) (B := (E : GL (Fin 5) K)) hxE hxy hAxm
    hAym
  exact (uq_conj_eq_one_iff h (by norm_num : 3 ≤ 5) A).2 ⟨w, hw⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
