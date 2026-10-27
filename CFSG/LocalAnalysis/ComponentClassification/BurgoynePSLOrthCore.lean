module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthNormal
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

theorem pow_conjAut_mul_fieldAut (D : GL (Fin n) K) (τ : K ≃+* K) (k : ℕ) :
    ∃ D' : GL (Fin n) K, (conjAut n K D * fieldAut n K τ) ^ k =
      conjAut n K D' * fieldAut n K (τ ^ k) := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨D', hD'⟩ := ih
    refine ⟨D' * GeneralLinearGroup.map ((τ ^ k : K ≃+* K) : K →+* K) D, ?_⟩
    rw [pow_succ, hD', map_mul, pow_succ, map_mul]
    calc conjAut n K D' * fieldAut n K (τ ^ k) * (conjAut n K D * fieldAut n K τ)
        = conjAut n K D' * (fieldAut n K (τ ^ k) * conjAut n K D) * fieldAut n K τ := by group
      _ = _ := by
          rw [LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_mul_conjAut]
          group

theorem pow_orderOf_eq_one_field [Finite K] (hn : 3 ≤ n) (D : GL (Fin n) K) (τ : K ≃+* K) :
    τ ^ orderOf (conjAut n K D * fieldAut n K τ) = 1 := by
  obtain ⟨D', hD'⟩ := pow_conjAut_mul_fieldAut D τ (orderOf (conjAut n K D * fieldAut n K τ))
  rw [pow_orderOf_eq_one] at hD'
  exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn D' _ hD'.symm).1

theorem exists_sq_add_sq [Finite K] (hK : ringChar K ≠ 2) (x : K) :
    ∃ a b : K, a ^ 2 + b ^ 2 = x := by
  have : Fintype K := Fintype.ofFinite K
  have hodd : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C x)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) _) hodd
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at hab
  linear_combination hab

theorem eq_one_of_fix_circle [Finite K] (hK : ringChar K ≠ 2) {τ : K ≃+* K}
    (h : ∀ a b : K, a ^ 2 + b ^ 2 = 1 → τ a = a) : τ = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsq : ∀ t : K, τ (t ^ 2) = t ^ 2 := by
    intro t
    by_cases ht : 1 + t ^ 2 = 0
    · have : t ^ 2 = -1 := by linear_combination ht
      rw [this, map_neg, map_one]
    · set a := (1 - t ^ 2) / (1 + t ^ 2) with ha
      have hcirc : a ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
        rw [ha]
        field_simp
        ring
      have hτa := h a _ hcirc
      have h1a : 1 + a ≠ 0 := by
        rw [ha]
        intro h0
        field_simp at h0
        exact h2 (by linear_combination h0)
      have ht2 : t ^ 2 = (1 - a) / (1 + a) := by
        rw [eq_div_iff h1a, ha]
        field_simp
        ring
      rw [ht2, map_div₀, map_sub, map_add, map_one, hτa]
  refine RingEquiv.ext fun x => ?_
  obtain ⟨a, b, rfl⟩ := exists_sq_add_sq hK x
  rw [map_add, hsq, hsq]
  rfl

theorem offDiag_eq_zero_of_commute_sign (h2 : (2 : K) ≠ 0) {I : Finset (Fin n)}
    (hI : 3 ≤ I.card) (hIc : ∀ x y, x ∉ I → y ∉ I → x = y) {D : Matrix (Fin n) (Fin n) K}
    (hs : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → D * signMat K {i, j} = signMat K {i, j} * D) :
    ∀ x y, x ≠ y → D x y = 0 := by
  have hpick : ∀ a b : Fin n, ∃ z ∈ I, z ≠ a ∧ z ≠ b := by
    intro a b
    have hcard : 0 < ((I.erase a).erase b).card := by
      have h1 := Finset.pred_card_le_card_erase (s := I) (a := a)
      have h2 := Finset.pred_card_le_card_erase (s := I.erase a) (a := b)
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.1 hcard
    simp only [Finset.mem_erase] at hz
    exact ⟨z, hz.2.2, hz.2.1, hz.1⟩
  intro x y hxy
  have key : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (y ∈ ({i, j} : Finset (Fin n)) ↔
      x ∉ ({i, j} : Finset (Fin n))) → D x y = 0 := by
    intro i hi j hj hij hxyij
    have e := congrFun (congrFun (hs i hi j hj hij) x) y
    simp only [signMat, mul_diagonal, diagonal_mul] at e
    by_cases hy : y ∈ ({i, j} : Finset (Fin n))
    · have hx := hxyij.1 hy
      simp only [hy, hx, ↓reduceIte] at e
      have : (2 : K) * D x y = 0 := by linear_combination -e
      exact (mul_eq_zero.1 this).resolve_left h2
    · have hx : x ∈ ({i, j} : Finset (Fin n)) := by
        by_contra hx
        exact hy (hxyij.2 hx)
      simp only [hy, hx, ↓reduceIte] at e
      have : (2 : K) * D x y = 0 := by linear_combination e
      exact (mul_eq_zero.1 this).resolve_left h2
  by_cases hyI : y ∈ I
  · obtain ⟨z, hzI, hzx, hzy⟩ := hpick x y
    refine key y hyI z hzI (Ne.symm hzy) ⟨fun _ => ?_, fun _ => by simp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hxy, Ne.symm hzx⟩
  · have hxI : x ∈ I := by
      by_contra hxI
      exact hxy (hIc x y hxI hyI)
    obtain ⟨z, hzI, hzx, hzy⟩ := hpick x y
    refine key x hxI z hzI (Ne.symm hzx) ⟨fun h => ?_, fun h => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact absurd h.symm hxy
      · exact absurd h.symm hzy
    · exact absurd (by simp) h

theorem conj_apply_diag_of_offDiag {D : GL (Fin n) K}
    (hD : ∀ x y, x ≠ y → (D : Matrix (Fin n) (Fin n) K) x y = 0) (M : Matrix (Fin n) (Fin n) K)
    (i : Fin n) :
    ((D : Matrix (Fin n) (Fin n) K) * M * ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i =
      M i i := by
  set Di := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have h1 : Di * (D : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDi : ∀ l, l ≠ i → Di l i = 0 := by
    intro l hl
    have e := congrFun (congrFun h1 l) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hD k i hk, mul_zero])
      (by simp), one_apply_ne hl] at e
    have hii : (D : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e
      have e' := congrFun (congrFun h1 i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hD k i hk, mul_zero])
        (by simp), h0, mul_zero, one_apply_eq] at e'
      exact zero_ne_one e'
    exact (mul_eq_zero.1 e).resolve_right hii
  have hii : Di i i * (D : Matrix (Fin n) (Fin n) K) i i = 1 := by
    have e := congrFun (congrFun h1 i) i
    rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hD k i hk, mul_zero])
      (by simp), one_apply_eq] at e
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hDi l hl, mul_zero])
    (by simp), Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [hD i k (Ne.symm hk), zero_mul]) (by simp)]
  linear_combination M i i * hii

theorem orth_centralizer [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n) {w : Fin n → K}
    (hw : OrthNF w) {D : GL (Fin n) K} {τ : K ≃+* K}
    (hodd : Odd (orderOf (conjAut n K D * fieldAut n K τ)))
    (hc : (conjAut n K D * fieldAut n K τ) * (conjAut n K (diagGL hw.1)⁻¹ * dualAut n K) =
      (conjAut n K (diagGL hw.1)⁻¹ * dualAut n K) * (conjAut n K D * fieldAut n K τ))
    (hex : ∀ G ∈ ⁅CatalogueBGraphForm.isometryGroup n K (diagGL hw.1),
        CatalogueBGraphForm.isometryGroup n K (diagGL hw.1)⁆,
      (D : Matrix (Fin n) (Fin n) K) * (G : Matrix (Fin n) (Fin n) K).map τ *
        ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = G) :
    conjAut n K D * fieldAut n K τ = 1 := by
  obtain ⟨hw0, I, hI3, hIc, hIw⟩ := hw
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Iso := CatalogueBGraphForm.isometryGroup n K (diagGL hw0) with hIso
  have hG : ∀ {i j : Fin n} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) {a b : K}
      (hab : a ^ 2 + b ^ 2 = 1), ⁅reflGL (K := K) i, rotGL i j hij hab⁆ ∈ ⁅Iso, Iso⁆ :=
    fun hi hj hij _ _ hab => commutator_mem_commutator (reflGL_mem hw0 _)
      (rotGL_mem hw0 hij (hIw _ hi _ hj) hab)
  have hS : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D : Matrix (Fin n) (Fin n) K) * signMat K {i, j} =
      signMat K {i, j} * D := by
    intro i hi j hj hij
    have hab : (0 : K) ^ 2 + 1 ^ 2 = 1 := by ring
    have e := hex _ (hG hi hj hij hab)
    rw [commutatorElement_reflGL_rotGL,
      show (0 : K) ^ 2 - 1 ^ 2 = -1 by ring, show -(2 * (0 : K) * 1) = 0 by ring,
      rotMat_neg_one_zero hij] at e
    have hmap : (signMat K {i, j}).map τ = signMat K {i, j} := by
      ext a b
      simp only [signMat, map_apply, diagonal_apply]
      split_ifs <;> simp
    rw [hmap] at e
    calc (D : Matrix (Fin n) (Fin n) K) * signMat K {i, j}
        = (D : Matrix (Fin n) (Fin n) K) * signMat K {i, j} *
          (((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = signMat K {i, j} * D := by rw [← Matrix.mul_assoc, e]
  have hdiag := offDiag_eq_zero_of_commute_sign h2 hI3 hIc hS
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ I, ∃ j ∈ I, i ≠ j := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I.card)
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by
      have := Finset.pred_card_le_card_erase (s := I) (a := i); omega : 0 < (I.erase i).card)
    exact ⟨i, hi, j, (Finset.mem_erase.1 hj).2, Ne.symm (Finset.mem_erase.1 hj).1⟩
  have hτk := pow_orderOf_eq_one_field hn D τ
  have hτ : τ = 1 := by
    refine eq_one_of_fix_circle hK fun a b hab => ?_
    have e := hex _ (hG hi hj hij hab)
    rw [commutatorElement_reflGL_rotGL] at e
    have e' := congrFun (congrFun e i) i
    rw [conj_apply_diag_of_offDiag hdiag, map_apply, rotMat_apply_left hij] at e'
    have hb : b ^ 2 = 1 - a ^ 2 := by linear_combination hab
    rw [hb] at e'
    have hτa2 : τ (a ^ 2) = a ^ 2 := by
      have e2 : τ (2 * a ^ 2 - 1) = 2 * a ^ 2 - 1 := by
        have h3 : (2 * a ^ 2 - 1 : K) = a ^ 2 - (1 - a ^ 2) := by ring
        rw [h3]
        exact e'
      rw [map_sub, map_mul, map_one, map_ofNat] at e2
      have : (2 : K) * (τ (a ^ 2) - a ^ 2) = 0 := by linear_combination e2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2)
    rw [map_pow] at hτa2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hτa2 with h | h
    · exact h
    · have hpow : ∀ m : ℕ, (τ ^ m) a = (-1) ^ m * a := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ]
          change (τ ^ m) (τ a) = _
          rw [h, map_neg, ih, pow_succ]
          ring
      have := hpow (orderOf (conjAut n K D * fieldAut n K τ))
      rw [hτk, hodd.neg_one_pow] at this
      change a = -1 * a at this
      have ha0 : a = 0 := by
        have : (2 : K) * a = 0 := by linear_combination this
        exact (mul_eq_zero.1 this).resolve_left h2
      rw [h, ha0, neg_zero]
  subst hτ
  rw [map_one, mul_one] at hc hodd ⊢
  set A₀ := (diagGL hw0)⁻¹ with hA₀
  have hsim : ∃ c : Kˣ, (D : Matrix (Fin n) (Fin n) K) * (A₀ : Matrix (Fin n) (Fin n) K) *
      (D : Matrix (Fin n) (Fin n) K)ᵀ = (c : K) • (A₀ : Matrix (Fin n) (Fin n) K) := by
    have h1 : conjAut n K D * conjAut n K A₀ * dualAut n K =
        conjAut n K A₀ * conjAut n K (GeneralLinearGroup.inverseTranspose D) * dualAut n K := by
      calc conjAut n K D * conjAut n K A₀ * dualAut n K
          = conjAut n K D * (conjAut n K A₀ * dualAut n K) := mul_assoc _ _ _
        _ = (conjAut n K A₀ * dualAut n K) * conjAut n K D := hc
        _ = conjAut n K A₀ * (dualAut n K * conjAut n K D) := mul_assoc _ _ _
        _ = conjAut n K A₀ * (conjAut n K (GeneralLinearGroup.inverseTranspose D) *
            dualAut n K) := by
            rw [LocalAnalysis.ComponentInitial.LinearFlag.dualAut_mul_conjAut]
        _ = _ := (mul_assoc _ _ _).symm
    have h2' : conjAut n K (D * A₀) =
        conjAut n K (A₀ * GeneralLinearGroup.inverseTranspose D) := by
      rw [map_mul, map_mul]
      exact mul_right_cancel h1
    have h1' : conjAut n K ((A₀ * GeneralLinearGroup.inverseTranspose D)⁻¹ * (D * A₀)) *
        fieldAut n K 1 = 1 := by
      rw [map_one, mul_one, map_mul, map_inv, h2', inv_mul_cancel]
    obtain ⟨-, c, hcs⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h1'
    refine ⟨c, ?_⟩
    have hDA : D * A₀ = A₀ * GeneralLinearGroup.inverseTranspose D *
        GeneralLinearGroup.scalar (Fin n) c := by
      rw [hcs, mul_inv_cancel_left]
    have hm := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K) *
      (D : Matrix (Fin n) (Fin n) K)ᵀ) hDA
    simp only [Units.val_mul] at hm
    rw [hm, GeneralLinearGroup.coe_inverseTranspose]
    have hsc : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (c : K) • 1 := by
      ext a b
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    rw [hsc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc,
      ← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one,
      Matrix.mul_one]
  obtain ⟨c, hcD⟩ := hsim
  have hA₀ij : (A₀ : Matrix (Fin n) (Fin n) K) = diagonal fun x => (w x)⁻¹ := rfl
  have hDd : (D : Matrix (Fin n) (Fin n) K) =
      diagonal fun x => (D : Matrix (Fin n) (Fin n) K) x x := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
    · rw [hdiag x y hxy, diagonal_apply_ne _ hxy]
  have hsq : ∀ x, (D : Matrix (Fin n) (Fin n) K) x x * D x x = c := by
    intro x
    rw [hDd, hA₀ij, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_smul] at hcD
    have e := congrFun (congrFun hcD x) x
    rw [diagonal_apply_eq, diagonal_apply_eq, Pi.smul_apply, smul_eq_mul] at e
    have hw' : (w x)⁻¹ ≠ 0 := inv_ne_zero (hw0 x)
    have : ((D : Matrix (Fin n) (Fin n) K) x x * D x x - c) * (w x)⁻¹ = 0 := by
      linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hw')
  have hD2 : conjAut n K (D * D) = 1 := by
    have : D * D = GeneralLinearGroup.scalar (Fin n) c := by
      apply Units.ext
      have hsc' : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = diagonal fun _ => (c : K) := rfl
      rw [Units.val_mul, hDd, diagonal_mul_diagonal, hsc']
      congr 1
      ext x
      exact hsq x
    rw [this, conjAut_scalar]
  have hord : orderOf (conjAut n K D) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two, ← map_mul, hD2]
  have h1 : orderOf (conjAut n K D) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

end CFSG.ComponentClassification.Burgoyne.PSL
