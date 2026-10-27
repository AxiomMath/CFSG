module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix Finset

open scoped Classical

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

@[expose] noncomputable def xL (x : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) L :=
  (x : Matrix (Fin 6) (Fin 6) K).map (algebraMap K L)

theorem xL_mul (x y : Matrix.SpecialLinearGroup (Fin 6) K) :
    xL (L := L) (x * y) = xL (L := L) x * xL (L := L) y := by
  unfold xL
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

theorem xL_one : xL (L := L) (1 : Matrix.SpecialLinearGroup (Fin 6) K) = 1 := by
  ext i j
  unfold xL
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply, h]

theorem xL_injective {x : Matrix.SpecialLinearGroup (Fin 6) K} (h : xL (L := L) x = 1) :
    x = 1 := by
  apply Subtype.ext
  ext i j
  have hij := congrFun (congrFun h i) j
  unfold xL at hij
  rw [Matrix.map_apply] at hij
  simp only [Matrix.SpecialLinearGroup.coe_one]
  apply (algebraMap K L).injective
  rw [hij]
  by_cases hi : i = j
  · subst hi
    simp
  · simp [Matrix.one_apply, hi]

theorem xL_map_sigma (σ : L →ₐ[K] L) (x : Matrix.SpecialLinearGroup (Fin 6) K) :
    (xL (L := L) x).map σ = xL (L := L) x := by
  unfold xL
  rw [Matrix.map_map]
  ext i j
  simp [Matrix.map_apply, AlgHom.commutes]

theorem diag_mul_apply {M N : Matrix (Fin 6) (Fin 6) L}
    (hM : ∀ i j, i ≠ j → M i j = 0) (hN : ∀ i j, i ≠ j → N i j = 0) (i : Fin 6) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [hM i k (Ne.symm hk), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem diag_mul_off {M N : Matrix (Fin 6) (Fin 6) L}
    (hM : ∀ i j, i ≠ j → M i j = 0) (hN : ∀ i j, i ≠ j → N i j = 0) :
    ∀ i j, i ≠ j → (M * N) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i = k
  · subst hik
    rw [hN i j hij, mul_zero]
  · rw [hM i k hik, zero_mul]

theorem diag_pow_apply {M : Matrix (Fin 6) (Fin 6) L}
    (hM : ∀ i j, i ≠ j → M i j = 0) (n : ℕ) :
    (∀ i j, i ≠ j → (M ^ n) i j = 0) ∧ (∀ i, (M ^ n) i i = M i i ^ n) := by
  induction n with
  | zero =>
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [pow_zero, Matrix.one_apply_ne hij]
    · rw [pow_zero, pow_zero, Matrix.one_apply_eq]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [pow_succ]
      exact diag_mul_off ih1 hM i j hij
    · rw [pow_succ, diag_mul_apply ih1 hM, ih2, pow_succ]

theorem card_filter_eq_count {ι : Type} [Fintype ι] (f : ι → L) (a : L) :
    (univ.filter fun i => f i = a).card = Multiset.count a (univ.val.map f) := by
  rw [Multiset.count_map, Finset.card, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro i _
  exact eq_comm

theorem count_symm {ι : Type} [Fintype ι] [DecidableEq ι] {ζ : L} (σ : L →ₐ[K] L) (hσζ : σ ζ = ζ ^ 2)
    (hσσ : ∀ u, σ (σ u) = u) (hζ3 : ζ ^ 3 = 1) (D : ι → L) (M : Matrix ι ι L)
    (hM : M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (D i)))
    (hσM : M.map σ = M) :
    (univ.filter fun i => D i = ζ).card = (univ.filter fun i => D i = ζ ^ 2).card := by
  have hσM' : M.map σ.toRingHom = M := hσM
  have hcp : (∏ i, (Polynomial.X - Polynomial.C (D i))).map σ.toRingHom =
      ∏ i, (Polynomial.X - Polynomial.C (D i)) := by
    rw [← hM]
    have := Matrix.charpoly_map M σ.toRingHom
    rw [hσM'] at this
    exact this.symm
  have hmul : (∏ i, (Polynomial.X - Polynomial.C (D i))) =
      ((univ.val.map D).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]
    rfl
  have hpoly : ((univ.val.map fun i => σ (D i)).map fun a => Polynomial.X - Polynomial.C a).prod =
      (((univ.val.map D).map fun a => Polynomial.X - Polynomial.C a).prod).map σ.toRingHom := by
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro i _
    simp [Function.comp_def, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have h2 : ((univ.val.map fun i => σ (D i)).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((univ.val.map D).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [hpoly]
    rw [hmul] at hcp
    exact hcp
  have hroots : univ.val.map (fun i => σ (D i)) = univ.val.map D := by
    have h1 := congrArg Polynomial.roots h2
    rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h1
  have hcount : Multiset.count ζ (univ.val.map (fun i => σ (D i))) =
      Multiset.count ζ (univ.val.map D) := by
    rw [hroots]
  rw [card_filter_eq_count D ζ, ← hcount, ← card_filter_eq_count (fun i => σ (D i)) ζ]
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro h
    calc D i = σ (σ (D i)) := (hσσ _).symm
      _ = σ ζ := by rw [h]
      _ = ζ ^ 2 := hσζ
  · intro h
    rw [h, map_pow, hσζ]
    calc (ζ ^ 2) ^ 2 = ζ * ζ ^ 3 := by ring
      _ = ζ := by rw [hζ3, mul_one]

@[expose] noncomputable def Dm (A : Matrix.GeneralLinearGroup (Fin 6) L) (x : Matrix.SpecialLinearGroup (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) L :=
  (A : Matrix (Fin 6) (Fin 6) L) * xL (L := L) x * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) :
    Matrix (Fin 6) (Fin 6) L)

theorem Dm_mul (A : Matrix.GeneralLinearGroup (Fin 6) L) (x y : Matrix.SpecialLinearGroup (Fin 6) K) :
    Dm A (x * y) = Dm A x * Dm A y := by
  have hinv : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
      (A : Matrix (Fin 6) (Fin 6) L) = 1 := Units.inv_mul A
  unfold Dm
  rw [xL_mul]
  rw [show (A : Matrix (Fin 6) (Fin 6) L) * xL (L := L) x *
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
      ((A : Matrix (Fin 6) (Fin 6) L) * xL (L := L) y *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L)) =
      (A : Matrix (Fin 6) (Fin 6) L) * xL (L := L) x *
        (((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
          (A : Matrix (Fin 6) (Fin 6) L)) * xL (L := L) y *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) by
      simp only [Matrix.mul_assoc]]
  rw [hinv, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem Dm_one (A : Matrix.GeneralLinearGroup (Fin 6) L) :
    Dm A (1 : Matrix.SpecialLinearGroup (Fin 6) K) = 1 := by
  have hinv : (A : Matrix (Fin 6) (Fin 6) L) *
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) = 1 :=
    Units.mul_inv A
  unfold Dm
  rw [xL_one, Matrix.mul_one, hinv]

theorem Dm_pow (A : Matrix.GeneralLinearGroup (Fin 6) L) (x : Matrix.SpecialLinearGroup (Fin 6) K)
    (n : ℕ) : Dm A (x ^ n) = Dm A x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Dm_one]
  | succ n ih => rw [pow_succ, pow_succ, Dm_mul, ih]

theorem diag_eigen [Finite L] {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (σ : L →ₐ[K] L) (hσζ : σ ζ = ζ ^ 2)
    (hσσ : ∀ u, σ (σ u) = u) (P : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K)) [Fintype P]
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hpow : ∀ x ∈ P, x ^ 3 = 1) :
    ∃ A : Matrix.GeneralLinearGroup (Fin 6) L,
      (∀ x : P, ∀ i j, i ≠ j → Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) i j = 0) ∧
      (∀ i (x y : P), Dm A ((x * y : P) : Matrix.SpecialLinearGroup (Fin 6) K) i i =
        Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) i i *
          Dm A (y : Matrix.SpecialLinearGroup (Fin 6) K) i i) ∧
      (∀ i (x : P), Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) i i ^ 3 = 1) ∧
      (∀ z : P, (univ.filter fun i => Dm A (z : Matrix.SpecialLinearGroup (Fin 6) K) i i = ζ).card =
        (univ.filter fun i => Dm A (z : Matrix.SpecialLinearGroup (Fin 6) K) i i = ζ ^ 2).card) ∧
      (∀ x : P, (∀ i, Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) i i = 1) → x = 1) := by
  let ι : Matrix.SpecialLinearGroup (Fin 6) K →* Matrix.SpecialLinearGroup (Fin 6) L :=
    Matrix.SpecialLinearGroup.map (algebraMap K L)
  have hι : ∀ x : Matrix.SpecialLinearGroup (Fin 6) K,
      (ι x : Matrix (Fin 6) (Fin 6) L) = xL (L := L) x := fun x => rfl
  let E₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 6) L) := P.map ι
  have hcomm' : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hpow' : ∀ x ∈ E₀, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  obtain ⟨A, hA⟩ :=
    CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ E₀ hcomm' hpow'
  have hoff : ∀ x ∈ P, ∀ i j, i ≠ j → Dm A x i j = 0 := by
    intro x hx i j hij
    exact hA (ι x) ⟨x, hx, rfl⟩ i j hij
  have hcoffx : ∀ x : P, ∀ i j, i ≠ j → Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) i j = 0 :=
    fun x i j hij => hoff x x.2 i j hij
  refine ⟨A, hcoffx, ?_, ?_, ?_, ?_⟩
  · intro i x y
    rw [Subgroup.coe_mul, Dm_mul]
    exact diag_mul_apply (hcoffx x) (hcoffx y) i
  · intro i x
    have h3 : (x : Matrix.SpecialLinearGroup (Fin 6) K) ^ 3 = 1 := hpow _ x.2
    have hdiag := (diag_pow_apply (hcoffx x) 3).2 i
    rw [← hdiag, ← Dm_pow, h3, Dm_one]
    simp
  · intro z
    have hchar : (xL (L := L) (z : Matrix.SpecialLinearGroup (Fin 6) K)).charpoly =
        ∏ i, (Polynomial.X - Polynomial.C (Dm A (z : Matrix.SpecialLinearGroup (Fin 6) K) i i)) := by
      have h1 : (Dm A (z : Matrix.SpecialLinearGroup (Fin 6) K)).charpoly =
          (xL (L := L) (z : Matrix.SpecialLinearGroup (Fin 6) K)).charpoly := by
        unfold Dm
        rw [Matrix.coe_units_inv]
        exact Matrix.charpoly_units_conj A _
      rw [← h1]
      have hdg : Dm A (z : Matrix.SpecialLinearGroup (Fin 6) K) =
          Matrix.diagonal (fun i => Dm A (z : Matrix.SpecialLinearGroup (Fin 6) K) i i) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · rw [Matrix.diagonal_apply_ne _ hij]
          exact hcoffx z i j hij
      rw [hdg, Matrix.charpoly_diagonal]
      simp only [Matrix.diagonal_apply_eq]
    exact count_symm (D := fun i => Dm A (z : Matrix.SpecialLinearGroup (Fin 6) K) i i)
      (M := xL (L := L) (z : Matrix.SpecialLinearGroup (Fin 6) K))
      σ hσζ hσσ hζ.pow_eq_one hchar (xL_map_sigma σ _)
  · intro x hx
    apply Subtype.ext
    show (x : Matrix.SpecialLinearGroup (Fin 6) K) = 1
    apply xL_injective (L := L)
    have hDm : Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq]
        exact hx i
      · rw [Matrix.one_apply_ne hij]
        exact hcoffx x i j hij
    unfold Dm at hDm
    calc xL (L := L) (x : Matrix.SpecialLinearGroup (Fin 6) K)
        = ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
            ((A : Matrix (Fin 6) (Fin 6) L) * xL (L := L) (x : Matrix.SpecialLinearGroup (Fin 6) K) *
              ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L)) *
            (A : Matrix (Fin 6) (Fin 6) L) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hDm, Matrix.mul_one, Units.inv_mul]


end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
