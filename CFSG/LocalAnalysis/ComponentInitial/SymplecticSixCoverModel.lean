module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl

variable {K : Type} [Field K]

section Coordinates

variable {n : ℕ}

theorem diagonal_mul_single (d : Fin n → K) (i j : Fin n) (a : K) :
    diagonal d * single i j a = single i j (d i * a) := by
  ext x y
  rw [diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · rw [h.1]
  · rw [mul_zero]

theorem single_mul_diagonal (d : Fin n → K) (i j : Fin n) (a : K) :
    single i j a * diagonal d = single i j (a * d j) := by
  ext x y
  rw [mul_diagonal, single_apply, single_apply]
  split_ifs with h
  · rw [h.2]
  · rw [zero_mul]

@[expose] def symCoord (i j : Fin n) (a : K) : Matrix (Fin n) (Fin n) K :=
  if i = j then single i i a else single i j a + single j i a

theorem symCoord_transpose (i j : Fin n) (a : K) : (symCoord i j a)ᵀ = symCoord i j a := by
  unfold symCoord
  split_ifs with h
  · rw [transpose_single]
  · rw [transpose_add, transpose_single, transpose_single, add_comm]

theorem symCoord_comm (i j : Fin n) (a : K) : symCoord i j a = symCoord j i a := by
  unfold symCoord
  by_cases h : i = j
  · subst h
    rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), add_comm]

theorem symCoord_add (i j : Fin n) (a b : K) :
    symCoord i j (a + b) = symCoord i j a + symCoord i j b := by
  unfold symCoord
  split_ifs
  · exact single_add _ _ _ _
  · rw [single_add, single_add]
    abel

theorem symCoord_zero (i j : Fin n) : symCoord i j (0 : K) = 0 := by
  unfold symCoord
  split_ifs <;> simp

theorem diagonal_mul_symCoord_mul_diagonal (d : Fin n → K) (i j : Fin n) (a : K) :
    diagonal d * symCoord i j a * diagonal d = symCoord i j (d i * d j * a) := by
  unfold symCoord
  split_ifs with h
  · subst h
    rw [diagonal_mul_single, single_mul_diagonal]
    congr 1
    ring
  · rw [Matrix.mul_add, Matrix.add_mul, diagonal_mul_single, diagonal_mul_single,
      single_mul_diagonal, single_mul_diagonal]
    congr 2 <;> ring

variable (n) in
theorem upperUnipotentSp_congr {C D : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C) (hD : Dᵀ = D)
    (h : C = D) : upperUnipotentSp n K hC = upperUnipotentSp n K hD := by
  subst h
  rfl

theorem upperUnipotentSp_mul {C D : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C) (hD : Dᵀ = D) :
    upperUnipotentSp n K hC * upperUnipotentSp n K hD =
      upperUnipotentSp n K (show (C + D)ᵀ = C + D by rw [transpose_add, hC, hD]) := by
  apply statedSp_ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp, coe_upperUnipotentSp,
    coe_upperUnipotentSp, fromBlocks_multiply]
  simp [add_comm]

theorem upperUnipotentSp_zero :
    upperUnipotentSp n K (show (0 : Matrix (Fin n) (Fin n) K)ᵀ = 0 from transpose_zero) = 1 := by
  apply statedSp_ext
  rw [coe_upperUnipotentSp, fromBlocks_one]
  rfl

theorem commute_upperUnipotentSp {C D : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C) (hD : Dᵀ = D) :
    upperUnipotentSp n K hC * upperUnipotentSp n K hD =
      upperUnipotentSp n K hD * upperUnipotentSp n K hC := by
  rw [upperUnipotentSp_mul, upperUnipotentSp_mul]
  exact upperUnipotentSp_congr n _ _ (add_comm C D)

theorem leviSp_mul_upperUnipotentSp_mul_inv (A : GL (Fin n) K) {C : Matrix (Fin n) (Fin n) K}
    (hC : Cᵀ = C) :
    leviSp A * upperUnipotentSp n K hC * (leviSp A)⁻¹ =
      upperUnipotentSp n K (show ((A : Matrix (Fin n) (Fin n) K) * C *
        (A : Matrix (Fin n) (Fin n) K)ᵀ)ᵀ = (A : Matrix (Fin n) (Fin n) K) * C *
          (A : Matrix (Fin n) (Fin n) K)ᵀ by
        rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  apply statedSp_ext
  have hA : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_leviSp,
    coe_leviSp, coe_upperUnipotentSp, coe_upperUnipotentSp, fromBlocks_multiply,
    fromBlocks_multiply, inv_inv]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  rw [hA, ← transpose_mul, hA, transpose_one]

@[expose] def tauCoord (i j : Fin n) (a : K) : StatedSp n K :=
  upperUnipotentSp n K (symCoord_transpose i j a)

theorem tauCoord_add (i j : Fin n) (a b : K) :
    tauCoord i j (a + b) = tauCoord i j a * tauCoord i j b := by
  rw [tauCoord, tauCoord, tauCoord, upperUnipotentSp_mul]
  exact upperUnipotentSp_congr n _ _ (symCoord_add i j a b)

theorem tauCoord_zero (i j : Fin n) : tauCoord i j (0 : K) = 1 := by
  rw [tauCoord, ← upperUnipotentSp_zero]
  exact upperUnipotentSp_congr n _ _ (symCoord_zero i j)

theorem tauCoord_comm (i j : Fin n) (a : K) : tauCoord i j a = tauCoord j i a :=
  upperUnipotentSp_congr n _ _ (symCoord_comm i j a)

theorem torusHom_mul_tauCoord_mul_inv (t : Fin n → Kˣ) (i j : Fin n) (a : K) :
    torusHom t * tauCoord i j a * (torusHom t)⁻¹ = tauCoord i j ((t i : K) * t j * a) := by
  change leviSp (TauCeti.diagGL t) * tauCoord i j a * (leviSp (TauCeti.diagGL t))⁻¹ = _
  rw [tauCoord, leviSp_mul_upperUnipotentSp_mul_inv, tauCoord]
  refine upperUnipotentSp_congr n _ _ ?_
  rw [TauCeti.diagGL_coe, diagonal_transpose, diagonal_mul_symCoord_mul_diagonal]

end Coordinates

theorem eq_sum_symCoord {B : Matrix (Fin 3) (Fin 3) K} (hB : Bᵀ = B) :
    B = symCoord 0 0 (B 0 0) + symCoord 1 1 (B 1 1) + symCoord 2 2 (B 2 2) +
      symCoord 0 1 (B 0 1) + symCoord 0 2 (B 0 2) + symCoord 1 2 (B 1 2) := by
  have h10 : B 1 0 = B 0 1 := by simpa using congrFun₂ hB 0 1
  have h20 : B 2 0 = B 0 2 := by simpa using congrFun₂ hB 0 2
  have h21 : B 2 1 = B 1 2 := by simpa using congrFun₂ hB 1 2
  ext x y
  fin_cases x <;> fin_cases y <;> simp [symCoord, h10, h20, h21]

theorem upperUnipotentSp_eq_prod_tauCoord {B : Matrix (Fin 3) (Fin 3) K} (hB : Bᵀ = B) :
    upperUnipotentSp 3 K hB = tauCoord 0 0 (B 0 0) * tauCoord 1 1 (B 1 1) *
      tauCoord 2 2 (B 2 2) * tauCoord 0 1 (B 0 1) * tauCoord 0 2 (B 0 2) *
      tauCoord 1 2 (B 1 2) := by
  simp only [tauCoord, upperUnipotentSp_mul]
  exact upperUnipotentSp_congr 3 _ _ (eq_sum_symCoord hB)

theorem exists_exponent_sep : ∀ i j k l : Fin 3, i ≤ j → k ≤ l → (i, j) ≠ (k, l) →
    ∃ e : Fin 3 → Fin 3, ((e k : ℤ) - 1) + ((e l : ℤ) - 1) = 0 ∧
      (((e i : ℤ) - 1) + ((e j : ℤ) - 1) = 1 ∨ ((e i : ℤ) - 1) + ((e j : ℤ) - 1) = 2) := by
  decide

theorem sq_ne_one_of_ne_one [CharP K 2] {r : K} (hr1 : r ≠ 1) : r ^ 2 ≠ 1 :=
  SymplecticCoverFour.sq_ne_one_of_charTwo hr1

theorem exists_weight_sep [CharP K 2] {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1) {i j k l : Fin 3}
    (hij : i ≤ j) (hkl : k ≤ l) (hne : (i, j) ≠ (k, l)) :
    ∃ t : Fin 3 → Kˣ, (t k : K) * t l = 1 ∧ (t i : K) * t j ≠ 1 := by
  obtain ⟨e, hkl', hij'⟩ := exists_exponent_sep i j k l hij hkl hne
  set u : Kˣ := Units.mk0 r hr0
  refine ⟨fun a => u ^ ((e a : ℤ) - 1), ?_, ?_⟩
  · rw [← Units.val_mul, ← _root_.zpow_add, hkl', zpow_zero, Units.val_one]
  · rw [← Units.val_mul, ← _root_.zpow_add]
    rcases hij' with h | h <;> rw [h]
    · rw [zpow_one]
      exact hr1
    · rw [zpow_two, Units.val_mul, ← sq]
      exact sq_ne_one_of_ne_one hr1

section Embedding

variable {m n : ℕ} (f : Fin m → Fin n)

@[expose] def inclMat : Matrix (Fin n) (Fin m) K :=
  Matrix.of fun a b => if a = f b then (1 : K) else 0

variable {f}

theorem inclMat_transpose_mul (hf : Function.Injective f) :
    (inclMat (K := K) f)ᵀ * inclMat (K := K) f = 1 := by
  ext b b'
  simp only [inclMat, mul_apply, transpose_apply, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (f b'), ite_eq_left (Finset.mem_univ _), one_apply]
  by_cases h : b = b'
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (hf h'.symm)), ite_eq_right h]

theorem inclMat_mul_single_mul_transpose (i j : Fin m) (a : K) :
    inclMat (K := K) f * single i j a * (inclMat (K := K) f)ᵀ = single (f i) (f j) a := by
  ext x y
  simp only [inclMat, mul_apply, transpose_apply, of_apply, single_apply]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · by_cases hx : x = f i <;> by_cases hy : y = f j <;> simp [hx, hy, eq_comm]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro c _ hc
    simp [Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem inclMat_mul_symCoord_mul_transpose (hf : Function.Injective f) (i j : Fin m) (a : K) :
    inclMat (K := K) f * symCoord i j a * (inclMat (K := K) f)ᵀ = symCoord (f i) (f j) a := by
  unfold symCoord
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, inclMat_mul_single_mul_transpose]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hf h')), Matrix.mul_add, Matrix.add_mul,
      inclMat_mul_single_mul_transpose, inclMat_mul_single_mul_transpose]

variable (f) in
@[expose] def blockIncl : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) K :=
  fromBlocks (inclMat (K := K) f) 0 0 (inclMat (K := K) f)

theorem blockIncl_transpose_mul (hf : Function.Injective f) :
    (blockIncl (K := K) f)ᵀ * blockIncl (K := K) f = 1 := by
  rw [blockIncl, fromBlocks_transpose, fromBlocks_multiply, inclMat_transpose_mul hf]
  simp [fromBlocks_one]

theorem symplecticJ_mul_blockIncl :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * blockIncl (K := K) f =
      blockIncl (K := K) f *
        (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  rw [blockIncl, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem blockIncl_transpose_mul_symplecticJ :
    (blockIncl (K := K) f)ᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (blockIncl (K := K) f)ᵀ := by
  rw [blockIncl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

variable (f) in
@[expose] def embedMat (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  1 + blockIncl (K := K) f * (g - 1) * (blockIncl (K := K) f)ᵀ

theorem embedMat_one : embedMat f (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
  simp [embedMat]

theorem embedMat_mul (hf : Function.Injective f) (g h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    embedMat f (g * h) = embedMat f g * embedMat f h := by
  simp only [embedMat]
  set P := blockIncl (K := K) f
  have hPP : Pᵀ * P = 1 := blockIncl_transpose_mul hf
  have e1 : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  have e2 : P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * ((g - 1) * (h - 1)) * Pᵀ := by
    calc P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * (g - 1) * (Pᵀ * P) * (h - 1) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = P * ((g - 1) * (h - 1)) * Pᵀ := by
          rw [hPP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e3 : P * (g * h - 1) * Pᵀ = P * (g - 1) * Pᵀ + P * (h - 1) * Pᵀ +
      P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) := by
    rw [e2, e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [e3]
  noncomm_ring

theorem embedMat_symplectic {g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hf : Function.Injective f) (hg : gᵀ * fromBlocks 0 1 (-1) 0 * g = fromBlocks 0 1 (-1) 0) :
    (embedMat f g)ᵀ * fromBlocks 0 1 (-1) 0 * embedMat f g = fromBlocks 0 1 (-1) 0 := by
  set P := blockIncl (K := K) f
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fromBlocks 0 1 (-1) 0
  set J' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := fromBlocks 0 1 (-1) 0
  have hPP : Pᵀ * P = 1 := blockIncl_transpose_mul hf
  have hJP : J * P = P * J' := symplecticJ_mul_blockIncl
  have hPJ : Pᵀ * J = J' * Pᵀ := blockIncl_transpose_mul_symplecticJ
  have hkey : (gᵀ - 1) * J' + J' * (g - 1) + (gᵀ - 1) * J' * (g - 1) = 0 := by
    have : (gᵀ - 1) * J' + J' * (g - 1) + (gᵀ - 1) * J' * (g - 1) = gᵀ * J' * g - J' := by
      noncomm_ring
    rw [this, hg, sub_self]
  have htr : (embedMat f g)ᵀ = 1 + P * (gᵀ - 1) * Pᵀ := by
    rw [embedMat, transpose_add, transpose_one, transpose_mul, transpose_mul, transpose_transpose,
      transpose_sub, transpose_one, Matrix.mul_assoc]
  rw [htr, embedMat]
  calc (1 + P * (gᵀ - 1) * Pᵀ) * J * (1 + P * (g - 1) * Pᵀ) =
      J + P * (gᵀ - 1) * (Pᵀ * J) + (J * P) * (g - 1) * Pᵀ +
        P * (gᵀ - 1) * (Pᵀ * J) * P * (g - 1) * Pᵀ := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
    _ = J + P * ((gᵀ - 1) * J' + J' * (g - 1) + (gᵀ - 1) * J' * (g - 1)) * Pᵀ := by
        rw [hPJ, hJP]
        have e : P * (gᵀ - 1) * (J' * Pᵀ) * P * (g - 1) * Pᵀ =
            P * ((gᵀ - 1) * J' * (g - 1)) * Pᵀ := by
          calc P * (gᵀ - 1) * (J' * Pᵀ) * P * (g - 1) * Pᵀ =
              P * (gᵀ - 1) * J' * (Pᵀ * P) * (g - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        rw [e]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel
    _ = J := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem embedMat_injective (hf : Function.Injective f) :
    Function.Injective (embedMat (K := K) f) := by
  intro g h hgh
  set P := blockIncl (K := K) f
  have hPP : Pᵀ * P = 1 := blockIncl_transpose_mul hf
  have key : ∀ g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K, Pᵀ * embedMat f g * P = g := by
    intro g
    rw [embedMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP]
    calc 1 + Pᵀ * (P * (g - 1) * Pᵀ) * P = 1 + (Pᵀ * P) * (g - 1) * (Pᵀ * P) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hPP, Matrix.one_mul, Matrix.mul_one, add_sub_cancel]
  rw [← key g, ← key h, hgh]

variable (f) in
@[expose] def embedGL (hf : Function.Injective f) :
    GL (Fin m ⊕ Fin m) K →* GL (Fin n ⊕ Fin n) K where
  toFun g :=
    { val := embedMat f (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      inv := embedMat f ((g⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      val_inv := by rw [← embedMat_mul hf, Units.mul_inv, embedMat_one]
      inv_val := by rw [← embedMat_mul hf, Units.inv_mul, embedMat_one] }
  map_one' := Units.ext embedMat_one
  map_mul' g h := Units.ext (embedMat_mul hf (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) h)

theorem coe_embedGL (hf : Function.Injective f) (g : GL (Fin m ⊕ Fin m) K) :
    ((embedGL f hf g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      embedMat f g :=
  rfl

variable (f) in
@[expose] def embedSp (hf : Function.Injective f) : StatedSp m K →* StatedSp n K :=
  ((embedGL f hf).comp (StatedSp m K).subtype).codRestrict (StatedSp n K) fun g =>
    (mem_statedSp_iff).2 (by
      rw [MonoidHom.comp_apply, coe_embedGL]
      exact embedMat_symplectic hf ((mem_statedSp_iff).1 g.2))

theorem coe_embedSp (hf : Function.Injective f) (g : StatedSp m K) :
    (((embedSp f hf g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      embedMat f ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
  rfl

theorem embedSp_injective (hf : Function.Injective f) :
    Function.Injective (embedSp (K := K) f hf) := fun g h hgh =>
  statedSp_ext (embedMat_injective hf (by
    rw [← coe_embedSp hf, ← coe_embedSp hf, hgh]))

theorem embedSp_tauCoord (hf : Function.Injective f) (i j : Fin m) (a : K) :
    embedSp f hf (tauCoord i j a) = tauCoord (f i) (f j) a := by
  apply statedSp_ext
  have hsub : (fromBlocks 1 (symCoord i j a) 0 1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 =
      fromBlocks 0 (symCoord i j a) 0 0 := by
    rw [← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp
  rw [coe_embedSp, tauCoord, tauCoord, coe_upperUnipotentSp, coe_upperUnipotentSp, embedMat, hsub,
    blockIncl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    ← inclMat_mul_symCoord_mul_transpose hf, ← fromBlocks_one, fromBlocks_add]
  simp

end Embedding

theorem isPerfect_statedSp_of_four_le (hK : 4 ≤ Nat.card K) (n : ℕ) :
    Group.IsPerfect (StatedSp n K) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin n K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin K n (Or.inl (Or.inr hK))
  let e : TauCeti.GLSymplecticFin n K ≃* StatedSp n K :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K).trans
      (MulEquiv.subgroupCongr
        (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n) (K := K)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem exists_mulEquiv_statedSp_three_of_lieModel {J : Type} [Group J] {f : ℕ}
    (hJ : CFSG.Blueprint.LieModel J .PSp 3 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (J ≃* StatedSp 3 K) := by
  rcases hJ with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hc
    have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (K := K)
      Nat.prime_two hf hK
    exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
      (SymplecticCoverFour.statedScalars_subgroupOf_eq_bot 3)).trans QuotientGroup.quotientBot)⟩⟩
  all_goals exact absurd h0 (by decide)

theorem upperUnipotentSp_eq_leviSp {n : ℕ} {C : Matrix (Fin n) (Fin n) K} (hC : Cᵀ = C)
    {A : GL (Fin n) K} (h : upperUnipotentSp n K hC = leviSp A) : C = 0 ∧ A = 1 := by
  have h' := congrArg (fun g : StatedSp n K => ((g : GL (Fin n ⊕ Fin n) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) h
  simp only [coe_upperUnipotentSp, coe_leviSp, fromBlocks_inj] at h'
  exact ⟨h'.2.1, Units.ext h'.1.symm⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover
