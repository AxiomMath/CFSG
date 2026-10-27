module

public import CFSG.LieType.Universal.Unitary.Extras.Basic

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras

section Form

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

@[expose] def aform (x y : Fin n → F) : F :=
  (fun a => σ (x a)) ⬝ᵥ (antidiag n *ᵥ y)

theorem antidiag_mulVec (y : Fin n → F) :
    antidiag n *ᵥ y = fun a => y (Fin.rev a) := by
  funext a
  simp [mulVec, dotProduct, antidiag, ite_mul, Finset.sum_ite_eq']

theorem vecMul_antidiag (w : Fin n → F) :
    w ᵥ* antidiag n = fun a => w (Fin.rev a) := by
  funext a
  simp only [vecMul, dotProduct, antidiag, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Fin.rev a)]
  · simp
  · intro b _ hb
    rw [ite_eq_right]
    intro h
    exact absurd (by rw [h, Fin.rev_rev]) hb
  · simp

theorem aform_apply (x y : Fin n → F) : aform σ x y = ∑ a, σ (x a) * y (Fin.rev a) := by
  rw [aform, antidiag_mulVec]
  rfl

theorem aform_add_left (x x' y : Fin n → F) :
    aform σ (x + x') y = aform σ x y + aform σ x' y := by
  simp only [aform_apply, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem aform_add_right (x y y' : Fin n → F) :
    aform σ x (y + y') = aform σ x y + aform σ x y' := by
  simp only [aform_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem aform_smul_left (c : F) (x y : Fin n → F) :
    aform σ (c • x) y = σ c * aform σ x y := by
  simp only [aform_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem aform_smul_right (c : F) (x y : Fin n → F) :
    aform σ x (c • y) = c * aform σ x y := by
  simp only [aform_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem aform_neg_left (x y : Fin n → F) : aform σ (-x) y = -aform σ x y := by
  simp only [aform_apply, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem aform_neg_right (x y : Fin n → F) : aform σ x (-y) = -aform σ x y := by
  simp only [aform_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem aform_zero_left (y : Fin n → F) : aform σ 0 y = 0 := by
  simp [aform_apply]

theorem aform_zero_right (x : Fin n → F) : aform σ x 0 = 0 := by
  simp [aform_apply]

theorem map_aform (hσ : ∀ c, σ (σ c) = c) (x y : Fin n → F) :
    σ (aform σ x y) = aform σ y x := by
  rw [aform_apply, aform_apply, map_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun a => ?_
  simp only [map_mul, hσ, Fin.revPerm_apply, Fin.rev_rev]
  ring

theorem aform_mulVec (M : Matrix (Fin n) (Fin n) F) (x y : Fin n → F) :
    aform σ (M *ᵥ x) (M *ᵥ y) =
      (fun a => σ (x a)) ⬝ᵥ ((conjTr σ M * antidiag n * M) *ᵥ y) := by
  rw [aform]
  have hx : (fun a => σ ((M *ᵥ x) a)) = M.map σ *ᵥ fun a => σ (x a) := by
    funext a
    simp [mulVec, dotProduct, map_sum]
  rw [hx, ← vecMul_transpose (M.map σ), ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rfl

theorem aform_single (a b : Fin n) :
    aform σ (Pi.single a 1) (Pi.single b 1) = antidiag n a b := by
  rw [aform]
  have : (fun c => σ ((Pi.single a (1 : F) : Fin n → F) c)) = Pi.single a 1 := by
    funext c
    by_cases hc : c = a
    · subst hc
      simp
    · simp [hc]
  rw [this, single_dotProduct, one_mul, mulVec_single_one, col_apply]

theorem aform_isometry_iff (M : Matrix (Fin n) (Fin n) F) :
    (∀ x y, aform σ (M *ᵥ x) (M *ᵥ y) = aform σ x y) ↔
      conjTr σ M * antidiag n * M = antidiag n := by
  constructor
  · intro hM
    ext a b
    have h := hM (Pi.single a 1) (Pi.single b 1)
    rw [aform_single, aform_mulVec] at h
    rw [← h]
    have : (fun c => σ ((Pi.single a (1 : F) : Fin n → F) c)) = Pi.single a 1 := by
      funext c
      by_cases hc : c = a
      · subst hc
        simp
      · simp [hc]
    rw [this, single_dotProduct, one_mul, mulVec_single_one, col_apply]
  · intro hM x y
    rw [aform_mulVec, hM]
    rfl

variable {σ} in
theorem aform_mat (g : SU σ n) (x y : Fin n → F) :
    aform σ (mat σ n g *ᵥ x) (mat σ n g *ᵥ y) = aform σ x y :=
  (aform_isometry_iff σ _).2 (conjTr_mat_mul g) x y

end Form

section Coord

variable {F : Type*} [Field F] {m : ℕ}

@[expose] def mid (j : Fin m) : Fin (m + 2) := ⟨j + 1, by omega⟩

theorem val_mid (j : Fin m) : (mid j : ℕ) = j + 1 := rfl

theorem mid_injective : Function.Injective (mid (m := m)) := fun a b h => by
  have := congrArg Fin.val h
  simp only [val_mid] at this
  exact Fin.ext (by omega)

theorem mid_ne_zero (j : Fin m) : mid j ≠ 0 := fun h => by
  have := congrArg Fin.val h
  simp [val_mid] at this

theorem mid_ne_last (j : Fin m) : mid j ≠ Fin.last (m + 1) := fun h => by
  have := congrArg Fin.val h
  simp only [val_mid, Fin.val_last] at this
  omega

theorem rev_mid (j : Fin m) : Fin.rev (mid j) = mid (Fin.rev j) := by
  apply Fin.ext
  simp only [Fin.val_rev, val_mid]
  omega

theorem zero_ne_last : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := fun h => by
  have := congrArg Fin.val h
  simp at this

theorem mem_range_mid {i : Fin (m + 2)} :
    i ∈ Set.range (mid (m := m)) ↔ 0 < (i : ℕ) ∧ (i : ℕ) < m + 1 := by
  constructor
  · rintro ⟨j, rfl⟩
    simp only [val_mid]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨⟨i - 1, by omega⟩, Fin.ext (by simp only [val_mid]; omega)⟩

@[expose] def midExt (w : Fin m → F) : Fin (m + 2) → F := fun i =>
  if h : 0 < (i : ℕ) ∧ (i : ℕ) < m + 1 then w ⟨i - 1, by omega⟩ else 0

theorem midExt_mid (w : Fin m → F) (j : Fin m) : midExt w (mid j) = w j := by
  have h : 0 < (mid j : ℕ) ∧ (mid j : ℕ) < m + 1 := by simp only [val_mid]; omega
  rw [midExt, dite_eq_left h]
  congr 1

theorem midExt_zero_apply (w : Fin m → F) : midExt w 0 = 0 := by
  simp [midExt]

theorem midExt_last (w : Fin m → F) : midExt w (Fin.last (m + 1)) = 0 := by
  simp [midExt]

theorem midExt_add (w w' : Fin m → F) : midExt (w + w') = midExt w + midExt w' := by
  funext i
  simp only [midExt, Pi.add_apply]
  split_ifs <;> simp

theorem midExt_zero : midExt (0 : Fin m → F) = 0 := by
  funext i
  simp only [midExt, Pi.zero_apply]
  split_ifs <;> rfl

theorem midExt_comp_mid {y : Fin (m + 2) → F} (h0 : y 0 = 0) (hl : y (Fin.last (m + 1)) = 0) :
    midExt (y ∘ mid) = y := by
  funext i
  by_cases h : 0 < (i : ℕ) ∧ (i : ℕ) < m + 1
  · rw [midExt, dite_eq_left h]
    simp only [Function.comp_apply]
    congr 1
    exact Fin.ext (by simp only [val_mid]; omega)
  · rw [midExt, dite_eq_right h]
    rcases Nat.lt_or_ge 0 (i : ℕ) with hi | hi
    · have : i = Fin.last (m + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      rw [this, hl]
    · have : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [this, h0]

end Coord

section Eichler

variable {F : Type*} [Field F] (σ : F ≃+* F) {m : ℕ}

abbrev e0 : Fin (m + 2) → F := Pi.single 0 1

abbrev eL : Fin (m + 2) → F := Pi.single (Fin.last (m + 1)) 1

theorem e0_last : (e0 : Fin (m + 2) → F) (Fin.last (m + 1)) = 0 :=
  Pi.single_eq_of_ne (Ne.symm zero_ne_last) 1

theorem eL_zero : (eL : Fin (m + 2) → F) 0 = 0 :=
  Pi.single_eq_of_ne zero_ne_last 1

theorem e0_apply_of_ne {i : Fin (m + 2)} (h : i ≠ 0) : (e0 : Fin (m + 2) → F) i = 0 :=
  Pi.single_eq_of_ne h 1

theorem eL_apply_of_ne {i : Fin (m + 2)} (h : i ≠ Fin.last (m + 1)) :
    (eL : Fin (m + 2) → F) i = 0 :=
  Pi.single_eq_of_ne h 1

theorem e0_ne_zero : (e0 : Fin (m + 2) → F) ≠ 0 := fun h => by
  have := congrFun h 0
  simp at this

theorem eL_ne_zero : (eL : Fin (m + 2) → F) ≠ 0 := fun h => by
  have := congrFun h (Fin.last (m + 1))
  simp at this

theorem aform_e0_left (y : Fin (m + 2) → F) : aform σ e0 y = y (Fin.last (m + 1)) := by
  rw [aform_apply, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem aform_e0_right (y : Fin (m + 2) → F) :
    aform σ y e0 = σ (y (Fin.last (m + 1))) := by
  rw [aform_apply, Finset.sum_eq_single (Fin.last (m + 1))]
  · simp
  · intro b _ hb
    have : Fin.rev b ≠ 0 := fun h => hb (by rw [← Fin.rev_rev b, h, Fin.rev_zero])
    simp [this]
  · simp

theorem aform_eL_left (y : Fin (m + 2) → F) : aform σ eL y = y 0 := by
  rw [aform_apply, Finset.sum_eq_single (Fin.last (m + 1))]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem aform_eL_right (y : Fin (m + 2) → F) : aform σ y eL = σ (y 0) := by
  rw [aform_apply, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    have : Fin.rev b ≠ Fin.last (m + 1) := fun h =>
      hb (by rw [← Fin.rev_rev b, h, Fin.rev_last])
    simp [this]
  · simp

@[expose] def eMat (y : Fin (m + 2) → F) (c : F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F :=
  1 + vecMulVec y eL + vecMulVec e0 (c • eL - (fun a => σ (y a)) ᵥ* antidiag (m + 2))

theorem eMat_mulVec (y : Fin (m + 2) → F) (c : F) (v : Fin (m + 2) → F) :
    eMat σ y c *ᵥ v =
      v + v (Fin.last (m + 1)) • y + (c * v (Fin.last (m + 1)) - aform σ y v) • e0 := by
  simp only [eMat, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, single_dotProduct,
    one_mul, sub_dotProduct, smul_dotProduct, smul_eq_mul, ← dotProduct_mulVec]
  rfl

theorem eMat_apply (y : Fin (m + 2) → F) (c : F) (i j : Fin (m + 2)) :
    eMat σ y c i j = (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) F) i j + y i * eL j +
      e0 i * (c * eL j - σ (y (Fin.rev j))) := by
  simp only [eMat, Matrix.add_apply, vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    vecMul_antidiag]

theorem eMat_apply_last {y : Fin (m + 2) → F} (hy0 : y 0 = 0) (c : F) (i : Fin (m + 2)) :
    eMat σ y c i (Fin.last (m + 1)) = eL i + y i + c * e0 i := by
  rw [eMat_apply, Fin.rev_last, hy0, map_zero, sub_zero]
  simp only [Pi.single_eq_same, mul_one]
  by_cases hi : i = Fin.last (m + 1)
  · subst hi
    simp
  · rw [one_apply_ne hi, eL_apply_of_ne hi]
    ring

theorem eMat_mulVec_eL {y : Fin (m + 2) → F} (hy0 : y 0 = 0) (c : F) :
    eMat σ y c *ᵥ eL = eL + y + c • e0 := by
  rw [eMat_mulVec, aform_eL_right, hy0, map_zero, sub_zero]
  simp

theorem eMat_zero : eMat σ (0 : Fin (m + 2) → F) 0 = 1 :=
  ext_iff_mulVec.2 fun v => by
    rw [eMat_mulVec, aform_zero_left, one_mulVec]
    simp

theorem eMat_mul {y y' : Fin (m + 2) → F} (hy : y (Fin.last (m + 1)) = 0)
    (hy' : y' (Fin.last (m + 1)) = 0) (c c' : F) :
    eMat σ y c * eMat σ y' c' = eMat σ (y + y') (c + c' - aform σ y y') := by
  refine ext_iff_mulVec.2 fun v => ?_
  have h1 : (eMat σ y' c' *ᵥ v) (Fin.last (m + 1)) = v (Fin.last (m + 1)) := by
    rw [eMat_mulVec]
    simp [hy']
  have h2 : aform σ y (eMat σ y' c' *ᵥ v) =
      aform σ y v + v (Fin.last (m + 1)) * aform σ y y' := by
    rw [eMat_mulVec, aform_add_right, aform_add_right, aform_smul_right, aform_smul_right,
      aform_e0_right, hy, map_zero, mul_zero, add_zero]
  rw [← mulVec_mulVec, eMat_mulVec σ y c (eMat σ y' c' *ᵥ v), h1, h2, eMat_mulVec σ y' c' v,
    eMat_mulVec, aform_add_left]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem det_eMat {y : Fin (m + 2) → F} (hy : y (Fin.last (m + 1)) = 0) (c : F) :
    (eMat σ y c).det = 1 := by
  rw [det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [eMat_apply, one_apply_eq]
    by_cases hl : i = Fin.last (m + 1)
    · subst hl
      simp [hy]
    · have h1 : (eL : Fin (m + 2) → F) i = 0 := eL_apply_of_ne hl
      by_cases h0 : i = 0
      · subst h0
        simp [Fin.rev_zero, hy]
      · simp [h1, e0_apply_of_ne h0]
  · intro i j hji
    simp only [id] at hji
    rw [eMat_apply, one_apply_ne (ne_of_gt hji)]
    have hj : j ≠ Fin.last (m + 1) := fun h => by
      rw [h] at hji
      exact absurd (Fin.le_last i) (not_le.2 hji)
    have hi : i ≠ 0 := fun h => by
      rw [h] at hji
      exact absurd (Fin.zero_le j) (not_le.2 hji)
    simp [eL_apply_of_ne hj, e0_apply_of_ne hi]

theorem eMat_isometry (hσ : ∀ c, σ (σ c) = c) {y : Fin (m + 2) → F}
    (hy : y (Fin.last (m + 1)) = 0) {c : F} (hc : c + σ c + aform σ y y = 0) :
    conjTr σ (eMat σ y c) * antidiag (m + 2) * eMat σ y c = antidiag (m + 2) := by
  refine (aform_isometry_iff σ _).1 fun v w => ?_
  rw [eMat_mulVec, eMat_mulVec]
  simp only [aform_add_left, aform_add_right, aform_smul_left, aform_smul_right, aform_e0_left,
    aform_e0_right, hy, e0_last, map_sub, map_mul, map_aform σ hσ y v, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]
  linear_combination (w (Fin.last (m + 1)) * σ (v (Fin.last (m + 1)))) * hc

theorem eMat_mul_eMat_neg {y : Fin (m + 2) → F} (hy : y (Fin.last (m + 1)) = 0) (c : F) :
    eMat σ y c * eMat σ (-y) (-c - aform σ y y) = 1 := by
  rw [eMat_mul σ hy (by simp [hy]), aform_neg_right, add_neg_cancel,
    show c + (-c - aform σ y y) - -aform σ y y = 0 by ring, eMat_zero]

theorem eMat_neg_mul_eMat {y : Fin (m + 2) → F} (hy : y (Fin.last (m + 1)) = 0) (c : F) :
    eMat σ (-y) (-c - aform σ y y) * eMat σ y c = 1 := by
  rw [eMat_mul σ (by simp [hy]) hy, aform_neg_left, neg_add_cancel,
    show -c - aform σ y y + c - -aform σ y y = 0 by ring, eMat_zero]

@[expose] def eGL {y : Fin (m + 2) → F} (hy : y (Fin.last (m + 1)) = 0) (c : F) :
    GL (Fin (m + 2)) F :=
  ⟨eMat σ y c, eMat σ (-y) (-c - aform σ y y), eMat_mul_eMat_neg σ hy c,
    eMat_neg_mul_eMat σ hy c⟩

@[expose] def eSU (hσ : ∀ c, σ (σ c) = c) {y : Fin (m + 2) → F}
    (hy : y (Fin.last (m + 1)) = 0) {c : F} (hc : c + σ c + aform σ y y = 0) :
    SU σ (m + 2) :=
  ⟨eGL σ hy c, mem_SU.2 ⟨det_eMat σ hy c, eMat_isometry σ hσ hy hc⟩⟩

theorem mat_eSU (hσ : ∀ c, σ (σ c) = c) {y : Fin (m + 2) → F}
    (hy : y (Fin.last (m + 1)) = 0) {c : F} (hc : c + σ c + aform σ y y = 0) :
    mat σ (m + 2) (eSU σ hσ hy hc) = eMat σ y c :=
  rfl

end Eichler

section Radical

variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {m : ℕ}

@[expose] def IsRadParam (y : Fin (m + 2) → F) (c : F) : Prop :=
  y 0 = 0 ∧ y (Fin.last (m + 1)) = 0 ∧ c + σ c + aform σ y y = 0

include hσ in
theorem IsRadParam.mul {y y' : Fin (m + 2) → F} {c c' : F} (h : IsRadParam σ y c)
    (h' : IsRadParam σ y' c') : IsRadParam σ (y + y') (c + c' - aform σ y y') := by
  refine ⟨by simp [h.1, h'.1], by simp [h.2.1, h'.2.1], ?_⟩
  rw [map_sub, map_add, map_aform σ hσ, aform_add_left, aform_add_right, aform_add_right]
  linear_combination h.2.2 + h'.2.2

include hσ in
theorem IsRadParam.inv {y : Fin (m + 2) → F} {c : F} (h : IsRadParam σ y c) :
    IsRadParam σ (-y) (-c - aform σ y y) := by
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  rw [map_sub, map_neg, map_aform σ hσ, aform_neg_left, aform_neg_right, neg_neg]
  linear_combination -h.2.2

theorem mat_inv_eq {n : ℕ} {g : SU σ n} {N : Matrix (Fin n) (Fin n) F} (h : mat σ n g * N = 1) :
    mat σ n g⁻¹ = N := by
  calc mat σ n g⁻¹ = mat σ n g⁻¹ * (mat σ n g * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

@[expose] def radical : Subgroup (SU σ (m + 2)) where
  carrier := {g | ∃ y c, IsRadParam σ y c ∧ mat σ (m + 2) g = eMat σ y c}
  mul_mem' := by
    rintro g g' ⟨y, c, h, hg⟩ ⟨y', c', h', hg'⟩
    exact ⟨_, _, h.mul σ hσ h', by rw [map_mul, hg, hg', eMat_mul σ h.2.1 h'.2.1]⟩
  one_mem' := ⟨0, 0, ⟨rfl, rfl, by simp [aform_zero_left]⟩, by rw [map_one, eMat_zero]⟩
  inv_mem' := by
    rintro g ⟨y, c, h, hg⟩
    exact ⟨_, _, h.inv σ hσ, mat_inv_eq σ (by rw [hg]; exact eMat_mul_eMat_neg σ h.2.1 c)⟩

@[expose] noncomputable def qθ (g : SU σ (m + 2)) : Fin m → F := fun j =>
  mat σ (m + 2) g (mid j) (Fin.last (m + 1))

@[expose] noncomputable def qc (g : SU σ (m + 2)) : F := mat σ (m + 2) g 0 (Fin.last (m + 1))

variable {σ hσ}

theorem qθ_of_eq {g : SU σ (m + 2)} {y : Fin (m + 2) → F} {c : F} (hy0 : y 0 = 0)
    (hg : mat σ (m + 2) g = eMat σ y c) : qθ σ g = y ∘ mid := by
  funext j
  show mat σ (m + 2) g (mid j) (Fin.last (m + 1)) = y (mid j)
  rw [hg, eMat_apply_last σ hy0, eL_apply_of_ne (mid_ne_last j), e0_apply_of_ne (mid_ne_zero j)]
  simp

theorem qc_of_eq {g : SU σ (m + 2)} {y : Fin (m + 2) → F} {c : F} (hy0 : y 0 = 0)
    (hg : mat σ (m + 2) g = eMat σ y c) : qc σ g = c := by
  rw [qc, hg, eMat_apply_last σ hy0, eL_zero, hy0]
  simp

theorem mem_radical_iff {g : SU σ (m + 2)} :
    g ∈ radical σ hσ ↔ IsRadParam σ (midExt (qθ σ g)) (qc σ g) ∧
      mat σ (m + 2) g = eMat σ (midExt (qθ σ g)) (qc σ g) := by
  constructor
  · rintro ⟨y, c, h, hg⟩
    rw [qθ_of_eq h.1 hg, qc_of_eq h.1 hg, midExt_comp_mid h.1 h.2.1]
    exact ⟨h, hg⟩
  · rintro ⟨h, hg⟩
    exact ⟨_, _, h, hg⟩

theorem trace_qc {g : SU σ (m + 2)} (hg : g ∈ radical σ hσ) :
    qc σ g + σ (qc σ g) + aform σ (midExt (qθ σ g)) (midExt (qθ σ g)) = 0 :=
  (mem_radical_iff.1 hg).1.2.2

theorem mat_of_mem_radical {g : SU σ (m + 2)} (hg : g ∈ radical σ hσ) :
    mat σ (m + 2) g = eMat σ (midExt (qθ σ g)) (qc σ g) :=
  (mem_radical_iff.1 hg).2

theorem eq_of_qθ_qc {g g' : SU σ (m + 2)} (hg : g ∈ radical σ hσ) (hg' : g' ∈ radical σ hσ)
    (h1 : qθ σ g = qθ σ g') (h2 : qc σ g = qc σ g') : g = g' :=
  mat_injective (by rw [mat_of_mem_radical hg, mat_of_mem_radical hg', h1, h2])

theorem qθ_mul {g g' : SU σ (m + 2)} (hg : g ∈ radical σ hσ) (hg' : g' ∈ radical σ hσ) :
    qθ σ (g * g') = qθ σ g + qθ σ g' := by
  have h := (mem_radical_iff.1 hg).1
  have h' := (mem_radical_iff.1 hg').1
  rw [qθ_of_eq (h.mul σ hσ h').1 (by rw [map_mul, mat_of_mem_radical hg,
    mat_of_mem_radical hg', eMat_mul σ h.2.1 h'.2.1]), ← midExt_add]
  funext j
  simp [midExt_mid]

theorem qc_mul {g g' : SU σ (m + 2)} (hg : g ∈ radical σ hσ) (hg' : g' ∈ radical σ hσ) :
    qc σ (g * g') = qc σ g + qc σ g' - aform σ (midExt (qθ σ g)) (midExt (qθ σ g')) := by
  have h := (mem_radical_iff.1 hg).1
  have h' := (mem_radical_iff.1 hg').1
  exact qc_of_eq (h.mul σ hσ h').1 (by rw [map_mul, mat_of_mem_radical hg,
    mat_of_mem_radical hg', eMat_mul σ h.2.1 h'.2.1])

theorem qθ_one : qθ σ (1 : SU σ (m + 2)) = 0 := by
  funext j
  simp [qθ, one_apply_ne (mid_ne_last j)]

theorem qc_one : qc σ (1 : SU σ (m + 2)) = 0 := by
  simp [qc, one_apply_ne (zero_ne_last (m := m))]

theorem qθ_inv {g : SU σ (m + 2)} (hg : g ∈ radical σ hσ) : qθ σ g⁻¹ = -qθ σ g := by
  have h := qθ_mul hg (inv_mem hg)
  rw [mul_inv_cancel, qθ_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem qθ_pow {g : SU σ (m + 2)} (hg : g ∈ radical σ hσ) (k : ℕ) :
    qθ σ (g ^ k) = k • qθ σ g := by
  induction k with
  | zero => rw [pow_zero, qθ_one, zero_smul]
  | succ k ih => rw [pow_succ, qθ_mul (pow_mem hg k) hg, ih, succ_nsmul]

theorem eq_one_of_mem_radical_of_mulVec_eL {g : SU σ (m + 2)} (hg : g ∈ radical σ hσ)
    (h : mat σ (m + 2) g *ᵥ eL = eL) : g = 1 := by
  obtain ⟨y, c, hp, hgm⟩ := hg
  rw [hgm, eMat_mulVec_eL σ hp.1, add_assoc, add_eq_left] at h
  have hc : c = 0 := by
    have := congrFun h 0
    simpa [hp.1] using this
  have hy : y = 0 := by
    rw [hc, zero_smul, add_zero] at h
    exact h
  refine mat_injective ?_
  rw [hgm, hy, hc, eMat_zero, map_one]

variable (σ hσ) in
@[expose] def center0 : Subgroup (SU σ (m + 2)) where
  carrier := {g | g ∈ radical σ hσ ∧ qθ σ g = 0}
  mul_mem' := by
    rintro g g' ⟨hg, h0⟩ ⟨hg', h0'⟩
    exact ⟨mul_mem hg hg', by rw [qθ_mul hg hg', h0, h0', add_zero]⟩
  one_mem' := ⟨one_mem _, qθ_one⟩
  inv_mem' := by
    rintro g ⟨hg, h0⟩
    exact ⟨inv_mem hg, by rw [qθ_inv hg, h0, neg_zero]⟩

theorem center0_le_radical : (center0 σ hσ : Subgroup (SU σ (m + 2))) ≤ radical σ hσ :=
  fun _ h => h.1

theorem trace_qc_of_mem_center0 {g : SU σ (m + 2)} (hg : g ∈ center0 σ hσ) :
    qc σ g + σ (qc σ g) = 0 := by
  have h := trace_qc hg.1
  rwa [hg.2, midExt_zero, aform_zero_left, add_zero] at h

theorem qc_mul_of_mem_center0 {z g : SU σ (m + 2)} (hz : z ∈ center0 σ hσ)
    (hg : g ∈ radical σ hσ) : qc σ (z * g) = qc σ z + qc σ g := by
  rw [qc_mul hz.1 hg, hz.2, midExt_zero, aform_zero_left, sub_zero]

theorem center0_comm {z g : SU σ (m + 2)} (hz : z ∈ center0 σ hσ) (hg : g ∈ radical σ hσ) :
    z * g = g * z := by
  refine eq_of_qθ_qc (mul_mem hz.1 hg) (mul_mem hg hz.1) ?_ ?_
  · rw [qθ_mul hz.1 hg, qθ_mul hg hz.1, add_comm]
  · rw [qc_mul hz.1 hg, qc_mul hg hz.1, hz.2, midExt_zero, aform_zero_left,
      aform_zero_right]
    ring

theorem qc_pow_of_mem_center0 {z : SU σ (m + 2)} (hz : z ∈ center0 σ hσ) (k : ℕ) :
    qc σ (z ^ k) = k * qc σ z := by
  induction k with
  | zero => rw [pow_zero, qc_one, Nat.cast_zero, zero_mul]
  | succ k ih =>
    rw [pow_succ', qc_mul_of_mem_center0 hz (pow_mem hz.1 k), ih]
    push_cast
    ring

variable (σ) in
@[expose] def levi : Subgroup (SU σ (m + 2)) where
  carrier := {g | (∃ a : F, mat σ (m + 2) g *ᵥ e0 = a • e0) ∧
    ∃ b : F, mat σ (m + 2) g *ᵥ eL = b • eL}
  mul_mem' := by
    rintro g g' ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
    refine ⟨⟨a' * a, ?_⟩, ⟨b' * b, ?_⟩⟩
    · rw [map_mul, ← mulVec_mulVec, ha', mulVec_smul, ha, smul_smul]
    · rw [map_mul, ← mulVec_mulVec, hb', mulVec_smul, hb, smul_smul]
  one_mem' := ⟨⟨1, by rw [map_one, one_mulVec, one_smul]⟩, ⟨1, by rw [map_one, one_mulVec,
    one_smul]⟩⟩
  inv_mem' := by
    rintro g ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have key : ∀ (v : Fin (m + 2) → F) (a : F), v ≠ 0 → mat σ (m + 2) g *ᵥ v = a • v →
        mat σ (m + 2) g⁻¹ *ᵥ v = a⁻¹ • v := by
      intro v a hv hav
      have h1 : v = a • (mat σ (m + 2) g⁻¹ *ᵥ v) := by
        rw [← mulVec_smul, ← hav, mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
          one_mulVec]
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at h1
        exact hv h1
      calc mat σ (m + 2) g⁻¹ *ᵥ v = a⁻¹ • (a • (mat σ (m + 2) g⁻¹ *ᵥ v)) := by
            rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
        _ = a⁻¹ • v := by rw [← h1]
    exact ⟨⟨a⁻¹, key _ a e0_ne_zero ha⟩, ⟨b⁻¹, key _ b eL_ne_zero hb⟩⟩

theorem scalar_ne_zero_of_mulVec {n : ℕ} {g : SU σ n} {v : Fin n → F} (hv : v ≠ 0) {a : F}
    (h : mat σ n g *ᵥ v = a • v) : a ≠ 0 := by
  rintro rfl
  have h1 : v = mat σ n g⁻¹ *ᵥ (mat σ n g *ᵥ v) := by
    rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]
  rw [h, zero_smul, mulVec_zero] at h1
  exact hv h1

variable (hσ) in
include hσ in
theorem mat_conj_eMat {g x : SU σ (m + 2)} {a : F} (ha : mat σ (m + 2) g *ᵥ e0 = a • e0)
    {y : Fin (m + 2) → F} {c : F} (hx : mat σ (m + 2) x = eMat σ y c) :
    mat σ (m + 2) (g * x * g⁻¹) = eMat σ (σ a • (mat σ (m + 2) g *ᵥ y)) (σ a * a * c) := by
  refine ext_iff_mulVec.2 fun v => ?_
  have hGw : mat σ (m + 2) g *ᵥ (mat σ (m + 2) g⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]
  have hwl : (mat σ (m + 2) g⁻¹ *ᵥ v) (Fin.last (m + 1)) = σ a * v (Fin.last (m + 1)) := by
    rw [← aform_e0_left σ (mat σ (m + 2) g⁻¹ *ᵥ v), ← aform_mat g e0, ha, hGw,
      aform_smul_left, aform_e0_left]
  have hyw : aform σ y (mat σ (m + 2) g⁻¹ *ᵥ v) = aform σ (mat σ (m + 2) g *ᵥ y) v := by
    rw [← aform_mat g y, hGw]
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hx, eMat_mulVec σ y c, mulVec_add,
    mulVec_add, mulVec_smul, mulVec_smul, hGw, ha, hwl, hyw,
    eMat_mulVec σ (σ a • (mat σ (m + 2) g *ᵥ y)) (σ a * a * c) v, aform_smul_left, hσ]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable (hσ) in
include hσ in
theorem IsRadParam.conj {g : SU σ (m + 2)} (hg : g ∈ levi σ) {a : F}
    (ha : mat σ (m + 2) g *ᵥ e0 = a • e0) {y : Fin (m + 2) → F} {c : F}
    (hp : IsRadParam σ y c) : IsRadParam σ (σ a • (mat σ (m + 2) g *ᵥ y)) (σ a * a * c) := by
  obtain ⟨-, ⟨b, hb⟩⟩ := hg
  have hσne : ∀ {t : F}, t ≠ 0 → σ t ≠ 0 := fun ht h => ht (σ.injective (by rw [h, map_zero]))
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (mat σ (m + 2) g *ᵥ y) 0 = 0 := by
      have h := aform_mat g eL y
      rw [hb, aform_smul_left, aform_eL_left, aform_eL_left, hp.1] at h
      exact (mul_eq_zero.1 h).resolve_left (hσne (scalar_ne_zero_of_mulVec eL_ne_zero hb))
    rw [Pi.smul_apply, h1, smul_zero]
  · have h1 : (mat σ (m + 2) g *ᵥ y) (Fin.last (m + 1)) = 0 := by
      have h := aform_mat g e0 y
      rw [ha, aform_smul_left, aform_e0_left, aform_e0_left, hp.2.1] at h
      exact (mul_eq_zero.1 h).resolve_left (hσne (scalar_ne_zero_of_mulVec e0_ne_zero ha))
    rw [Pi.smul_apply, h1, smul_zero]
  · rw [aform_smul_left, aform_smul_right, aform_mat g y y]
    simp only [map_mul, hσ]
    linear_combination (σ a * a) * hp.2.2

theorem conj_mem_radical {g x : SU σ (m + 2)} (hg : g ∈ levi σ) (hx : x ∈ radical σ hσ) :
    g * x * g⁻¹ ∈ radical σ hσ := by
  obtain ⟨⟨a, ha⟩, -⟩ := id hg
  exact ⟨_, _, (mem_radical_iff.1 hx).1.conj hσ hg ha,
    mat_conj_eMat hσ ha (mat_of_mem_radical hx)⟩

theorem qθ_conj {g x : SU σ (m + 2)} (hg : g ∈ levi σ) {a : F}
    (ha : mat σ (m + 2) g *ᵥ e0 = a • e0) (hx : x ∈ radical σ hσ) :
    qθ σ (g * x * g⁻¹) = fun j => σ a * (mat σ (m + 2) g *ᵥ midExt (qθ σ x)) (mid j) := by
  rw [qθ_of_eq ((mem_radical_iff.1 hx).1.conj hσ hg ha).1
    (mat_conj_eMat hσ ha (mat_of_mem_radical hx))]
  rfl

theorem qc_conj {g x : SU σ (m + 2)} (hg : g ∈ levi σ) {a : F}
    (ha : mat σ (m + 2) g *ᵥ e0 = a • e0) (hx : x ∈ radical σ hσ) :
    qc σ (g * x * g⁻¹) = σ a * a * qc σ x :=
  qc_of_eq ((mem_radical_iff.1 hx).1.conj hσ hg ha).1
    (mat_conj_eMat hσ ha (mat_of_mem_radical hx))

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {H Q' : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ Q', g * x * g⁻¹ ∈ Q') : H ≤ Subgroup.normalizer (Q' : Set G) :=
  fun g hg => Subgroup.mem_normalizer_iff.2 fun x => ⟨h g hg x, fun hx => by
    have h1 := h g⁻¹ (inv_mem hg) _ hx
    rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1⟩

theorem levi_le_normalizer_radical :
    levi σ ≤ Subgroup.normalizer (((radical σ hσ : Subgroup (SU σ (m + 2)))) :
      Set (SU σ (m + 2))) :=
  le_normalizer_of_conj_mem fun _ hg _ hx => conj_mem_radical hg hx

theorem levi_le_normalizer_center0 :
    levi σ ≤ Subgroup.normalizer (((center0 σ hσ : Subgroup (SU σ (m + 2)))) :
      Set (SU σ (m + 2))) := by
  refine le_normalizer_of_conj_mem fun g hg x hx => ⟨conj_mem_radical hg hx.1, ?_⟩
  obtain ⟨⟨a, ha⟩, -⟩ := id hg
  rw [qθ_conj hg ha hx.1, hx.2, midExt_zero, mulVec_zero]
  funext j
  simp

end Radical

section CharThree

variable {F : Type*} [Field F] [CharP F 3] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {m : ℕ}

theorem three_eq_zero : (3 : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F 3

include hσ in
theorem aform_self_trace (y : Fin (m + 2) → F) :
    aform σ y y + σ (aform σ y y) + aform σ y y = 0 := by
  rw [map_aform σ hσ]
  linear_combination aform σ y y * (three_eq_zero (F := F))

@[expose] noncomputable def lift (w : Fin m → F) : SU σ (m + 2) :=
  eSU σ hσ (midExt_last w) (aform_self_trace hσ (midExt w))

theorem lift_mem (w : Fin m → F) : lift hσ w ∈ radical σ hσ :=
  ⟨_, _, ⟨midExt_zero_apply w, midExt_last w, aform_self_trace hσ (midExt w)⟩, rfl⟩

theorem qθ_lift (w : Fin m → F) : qθ σ (lift hσ w) = w := by
  rw [qθ_of_eq (g := lift hσ w) (midExt_zero_apply w)
    (mat_eSU σ hσ (midExt_last w) (aform_self_trace hσ (midExt w)))]
  funext j
  exact midExt_mid w j

theorem pow_three_mem_center0 {g : SU σ (m + 2)} (hg : g ∈ radical σ hσ) :
    g ^ 3 ∈ center0 σ hσ := by
  refine ⟨pow_mem hg 3, ?_⟩
  rw [qθ_pow hg]
  funext j
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat, three_eq_zero,
    zero_mul]

theorem pow_three_eq_one {z : SU σ (m + 2)} (hz : z ∈ center0 σ hσ) : z ^ 3 = 1 := by
  refine eq_of_qθ_qc (pow_mem hz.1 3) (one_mem _) ?_ ?_
  · rw [qθ_pow hz.1, hz.2, smul_zero, qθ_one]
  · rw [qc_pow_of_mem_center0 hz, qc_one, Nat.cast_ofNat, three_eq_zero, zero_mul]

theorem card_radical [Finite F] :
    Nat.card (radical σ hσ (m := m)) = Nat.card (Fin m → F) * Nat.card (traceZero σ) := by
  rw [← Nat.card_prod]
  have hmem : ∀ q : (Fin m → F) × traceZero σ, IsRadParam σ (midExt q.1)
      ((q.2 : F) + aform σ (midExt q.1) (midExt q.1)) := fun q => by
    refine ⟨midExt_zero_apply _, midExt_last _, ?_⟩
    rw [map_add, map_aform σ hσ]
    linear_combination ((mem_traceZero σ).1 q.2.2) +
      aform σ (midExt q.1) (midExt q.1) * (three_eq_zero (F := F))
  let Φ : (Fin m → F) × traceZero σ → radical σ hσ (m := m) := fun q =>
    ⟨eSU σ hσ (hmem q).2.1 (hmem q).2.2, _, _, hmem q, rfl⟩
  have hθ : ∀ q, qθ σ (Φ q : SU σ (m + 2)) = q.1 := fun q => by
    rw [qθ_of_eq (hmem q).1 (mat_eSU σ hσ (hmem q).2.1 (hmem q).2.2)]
    funext j
    exact midExt_mid q.1 j
  have hc : ∀ q, qc σ (Φ q : SU σ (m + 2)) = q.2 + aform σ (midExt q.1) (midExt q.1) :=
    fun q => qc_of_eq (hmem q).1 (mat_eSU σ hσ (hmem q).2.1 (hmem q).2.2)
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨fun q q' h => ?_, fun g => ?_⟩).symm
  · have h1 : q.1 = q'.1 := by rw [← hθ q, ← hθ q', h]
    have h2 := hc q
    rw [h, hc q', h1] at h2
    exact Prod.ext h1 (Subtype.ext (add_right_cancel h2).symm)
  · have ht : qc σ (g : SU σ (m + 2)) - aform σ (midExt (qθ σ (g : SU σ (m + 2))))
        (midExt (qθ σ (g : SU σ (m + 2)))) ∈ traceZero σ := by
      rw [mem_traceZero σ, map_sub, map_aform σ hσ]
      linear_combination trace_qc g.2 - aform σ (midExt (qθ σ (g : SU σ (m + 2))))
        (midExt (qθ σ (g : SU σ (m + 2)))) * (three_eq_zero (F := F))
    refine ⟨(qθ σ (g : SU σ (m + 2)), ⟨_, ht⟩),
      Subtype.ext (eq_of_qθ_qc (Φ _).2 g.2 (hθ _) ?_)⟩
    rw [hc]
    simp

omit [CharP F 3] in
theorem card_center0 :
    Nat.card (center0 σ hσ (m := m)) = Nat.card (traceZero σ) := by
  have hmem : ∀ c : traceZero σ, IsRadParam σ (0 : Fin (m + 2) → F) c := fun c =>
    ⟨rfl, rfl, by rw [aform_zero_left, add_zero]; exact (mem_traceZero σ).1 c.2⟩
  let Φ : traceZero σ → center0 σ hσ (m := m) := fun c =>
    ⟨eSU σ hσ (hmem c).2.1 (hmem c).2.2, ⟨_, _, hmem c, rfl⟩, by
      rw [qθ_of_eq rfl (mat_eSU σ hσ (hmem c).2.1 (hmem c).2.2)]
      rfl⟩
  have hc : ∀ c, qc σ (Φ c : SU σ (m + 2)) = c := fun c =>
    qc_of_eq rfl (mat_eSU σ hσ (hmem c).2.1 (hmem c).2.2)
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨fun c c' h => Subtype.ext ?_, fun z => ?_⟩).symm
  · rw [← hc c, ← hc c', h]
  · refine ⟨⟨qc σ (z : SU σ (m + 2)), (mem_traceZero σ).2 (trace_qc_of_mem_center0 z.2)⟩,
      Subtype.ext (eq_of_qθ_qc (Φ _).2.1 z.2.1 (by rw [(Φ _).2.2, z.2.2]) (hc _))⟩

end CharThree

end CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
