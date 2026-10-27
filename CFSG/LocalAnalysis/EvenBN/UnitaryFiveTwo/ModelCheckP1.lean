module

import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA2

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def zSU : SU52 := x₄SU 0 1 zero_one_rel

theorem mat_zSU : mat zSU = x₄Mat 0 1 := rfl

theorem zSU_mem : zSU ∈ ZX₄sub := mem_x₄Sub.2 ⟨0, 1, rfl, rfl⟩

theorem fld_zSU : fld zSU = zSU := ext_mat (by rw [mat_fld, mat_zSU]; decide)

@[expose] def IsBlk (M : Matrix (Fin 5) (Fin 5) F4) : Prop :=
  (∀ j : Fin 5, j ≠ 0 → M 0 j = 0) ∧ ∀ i : Fin 5, i ≠ 4 → M i 4 = 0

@[expose] def IsA₁Shape (N : Matrix (Fin 5) (Fin 5) F4) : Prop :=
  ∀ i j : Fin 5, ¬ ((j = 0 ∧ i ≠ 0) ∨ (i = 4 ∧ j ≠ 4)) → N i j = 0

theorem entry_of_comm {M X : Matrix (Fin 5) (Fin 5) F4} (h : M * X = X * M) (i j : Fin 5) :
    ∑ k, M i k * X k j = ∑ k, X i k * M k j := by
  have := congrFun (congrFun h i) j
  simpa [Matrix.mul_apply] using this

theorem isBlk_of_comm_x₄ {M : Matrix (Fin 5) (Fin 5) F4} (h : M * x₄Mat 0 1 = x₄Mat 0 1 * M) :
    IsBlk M ∧ M 0 0 = M 4 4 := by
  refine ⟨⟨fun j hj => ?_, fun i hi => ?_⟩, ?_⟩
  · have e := entry_of_comm h 4 j
    fin_cases j
    · exact absurd rfl hj
    all_goals simpa [Fin.sum_univ_five, x₄Mat] using e.symm
  · have e := entry_of_comm h i 0
    fin_cases i
    all_goals first
      | exact absurd rfl hi
      | simpa [Fin.sum_univ_five, x₄Mat] using e
  · have e := entry_of_comm h 4 0
    simp [Fin.sum_univ_five, x₄Mat] at e
    linear_combination e.symm

theorem isBlk_of_comm_z {g : SU52} (hg : g * zSU = zSU * g) :
    IsBlk (mat g) ∧ mat g 0 0 = mat g 4 4 :=
  isBlk_of_comm_x₄ (by rw [← mat_zSU, ← mat_mul, ← mat_mul, hg])

theorem isA₁Shape_mul {P N Q : Matrix (Fin 5) (Fin 5) F4} (hP : IsBlk P) (hQ : IsBlk Q)
    (hN : IsA₁Shape N) : IsA₁Shape (P * N * Q) := by
  intro i j hij
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  by_cases hkl : (l = 0 ∧ k ≠ 0) ∨ (k = 4 ∧ l ≠ 4)
  · rcases hkl with ⟨rfl, hk⟩ | ⟨rfl, hl⟩
    · by_cases hj : j = 0
      · subst hj
        have hi : i = 0 := by
          by_contra hi
          exact hij (Or.inl ⟨rfl, hi⟩)
        subst hi
        rw [hP.1 k hk, zero_mul, zero_mul]
      · rw [hQ.1 j hj, mul_zero]
    · by_cases hi : i = 4
      · subst hi
        have hj : j = 4 := by
          by_contra hj
          exact hij (Or.inr ⟨rfl, hj⟩)
        subst hj
        rw [hQ.2 l hl, mul_zero]
      · rw [hP.2 i hi, zero_mul, zero_mul]
  · rw [hN k l hkl, mul_zero, zero_mul]

theorem isA₁Shape_x₂ (a : F4) : IsA₁Shape (x₂Mat a - 1) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [x₂Mat] at hij ⊢

theorem isA₁Shape_x₃ (a : F4) : IsA₁Shape (x₃Mat a - 1) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [x₃Mat] at hij ⊢

theorem isA₁Shape_x₄ (a b : F4) : IsA₁Shape (x₄Mat a b - 1) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [x₄Mat] at hij ⊢

theorem mem_A₁sub_of_shape {g : SU52} (h : IsA₁Shape (mat g - 1)) : g ∈ A₁sub := by
  have key : ∀ i j : Fin 5, ¬ ((j = 0 ∧ i ≠ 0) ∨ (i = 4 ∧ j ≠ 4)) →
      mat g i j = (1 : Matrix (Fin 5) (Fin 5) F4) i j := fun i j hij => by
    have := h i j hij
    rwa [Matrix.sub_apply, sub_eq_zero] at this
  rw [mem_A₁sub, Ssub_eq_LTsub, mem_LTsub]
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [key i j (by revert i j; decide), Matrix.one_apply_ne (ne_of_lt hij)]
  · rw [key i i (by revert i; decide), Matrix.one_apply_eq]
  · rw [key 2 1 (by decide)]
    rfl
  · rw [key 3 1 (by decide)]
    rfl

theorem conj_mem_A₁sub_of_shape {g a : SU52} (hg : g * zSU = zSU * g)
    (ha : IsA₁Shape (mat a - 1)) : g * a * g⁻¹ ∈ A₁sub := by
  apply mem_A₁sub_of_shape
  have hgi : g⁻¹ * zSU = zSU * g⁻¹ := by
    calc g⁻¹ * zSU = g⁻¹ * (zSU * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * zSU) * g⁻¹ := by rw [hg]
      _ = zSU * g⁻¹ := by group
  have hgg : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  have e : mat (g * a * g⁻¹) - 1 = mat g * (mat a - 1) * mat g⁻¹ := by
    simp only [mat_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hgg]
  rw [e]
  exact isA₁Shape_mul (isBlk_of_comm_z hg).1 (isBlk_of_comm_z hgi).1 ha

theorem conj_mem_A₁sub_of_comm_z {g : SU52} (hg : g * zSU = zSU * g) {a : SU52}
    (ha : a ∈ A₁sub) : g * a * g⁻¹ ∈ A₁sub := by
  have hle : A₁sub ≤ A₁sub.comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx
    · obtain ⟨c, hc⟩ := mem_X₂sub.1 hx
      exact conj_mem_A₁sub_of_shape hg (by rw [hc]; exact isA₁Shape_x₂ c)
    · obtain ⟨c, hc⟩ := mem_X₃sub.1 hx
      exact conj_mem_A₁sub_of_shape hg (by rw [hc]; exact isA₁Shape_x₃ c)
    · obtain ⟨c, c', hc⟩ := mem_X₄sub.1 hx
      exact conj_mem_A₁sub_of_shape hg (by rw [hc]; exact isA₁Shape_x₄ c c')
  exact hle ha

theorem X₂sub_le_A₁sub : X₂sub ≤ A₁sub := le_sup_left.trans le_sup_left

theorem X₃sub_le_A₁sub : X₃sub ≤ A₁sub := le_sup_right.trans le_sup_left

theorem X₄sub_le_A₁sub' : X₄sub ≤ A₁sub := le_sup_right

theorem eq_one_of_pow_five : ∀ c : F4, c ^ 5 = 1 → c = 1 := by decide


theorem eq_of_comm_A₁_gens {M : Matrix (Fin 5) (Fin 5) F4}
    (hz : M * x₄Mat 0 1 = x₄Mat 0 1 * M) (e₂ : M * x₂Mat 1 = x₂Mat 1 * M)
    (e₂' : M * x₂Mat F4.ω = x₂Mat F4.ω * M) (e₃ : M * x₃Mat 1 = x₃Mat 1 * M)
    (e₃' : M * x₃Mat F4.ω = x₃Mat F4.ω * M) (e₄ : M * x₄Mat 1 F4.ω = x₄Mat 1 F4.ω * M)
    (e₄' : M * x₄Mat F4.ω F4.ω = x₄Mat F4.ω F4.ω * M) (i j : Fin 5) :
    M i j = if i = j then M 0 0 else if i = 4 ∧ j = 0 then M 4 0 else 0 := by
  obtain ⟨⟨h0, h4⟩, h04⟩ := isBlk_of_comm_x₄ hz
  have z01 := h0 1 (by decide)
  have z02 := h0 2 (by decide)
  have z03 := h0 3 (by decide)
  have z04 := h0 4 (by decide)
  have z14 := h4 1 (by decide)
  have z24 := h4 2 (by decide)
  have z34 := h4 3 (by decide)
  have a10 := entry_of_comm e₂ 1 0
  simp [Fin.sum_univ_five, x₂Mat] at a10
  have a20 := entry_of_comm e₂ 2 0
  simp [Fin.sum_univ_five, x₂Mat] at a20
  have a30 := entry_of_comm e₂ 3 0
  simp [Fin.sum_univ_five, x₂Mat] at a30
  have a40 := entry_of_comm e₂ 4 0
  simp [Fin.sum_univ_five, x₂Mat] at a40
  have b40 := entry_of_comm e₂' 4 0
  simp [Fin.sum_univ_five, x₂Mat, bar_ω] at b40
  have c10 := entry_of_comm e₃ 1 0
  simp [Fin.sum_univ_five, x₃Mat] at c10
  have c30 := entry_of_comm e₃ 3 0
  simp [Fin.sum_univ_five, x₃Mat] at c30
  have c40 := entry_of_comm e₃ 4 0
  simp [Fin.sum_univ_five, x₃Mat] at c40
  have d40 := entry_of_comm e₃' 4 0
  simp [Fin.sum_univ_five, x₃Mat, bar_ω] at d40
  have c42 := entry_of_comm e₃ 4 2
  simp [Fin.sum_univ_five, x₃Mat] at c42
  have f20 := entry_of_comm e₄ 2 0
  simp [Fin.sum_univ_five, x₄Mat, z24] at f20
  have f30 := entry_of_comm e₄ 3 0
  simp [Fin.sum_univ_five, x₄Mat, z34] at f30
  have f40 := entry_of_comm e₄ 4 0
  simp [Fin.sum_univ_five, x₄Mat] at f40
  have g40 := entry_of_comm e₄' 4 0
  simp [Fin.sum_univ_five, x₄Mat, bar_ω] at g40
  have f41 := entry_of_comm e₄ 4 1
  simp [Fin.sum_univ_five, x₄Mat, z01] at f41
  have f43 := entry_of_comm e₄ 4 3
  simp [Fin.sum_univ_five, x₄Mat, z03] at f43
  have m11 : M 1 1 = M 0 0 := by linear_combination a10
  have m21 : M 2 1 = 0 := by linear_combination a20
  have m31 : M 3 1 = 0 := by linear_combination a30
  have m30 : M 3 0 = 0 := by linear_combination F4.ω * a40 - b40
  have m41 : M 4 1 = 0 := by linear_combination (1 + F4.ω) * a40 - b40
  have m13 : M 1 3 = 0 := by linear_combination c10
  have m33 : M 3 3 = M 0 0 := by linear_combination c30
  have m10 : M 1 0 = 0 := by linear_combination F4.ω * c40 - d40
  have m43 : M 4 3 = 0 := by linear_combination (1 + F4.ω) * c40 - d40
  have m12 : M 1 2 = 0 := by linear_combination c42
  have m22 : M 2 2 = M 0 0 := by linear_combination f20
  have m32 : M 3 2 = 0 := by linear_combination f30
  have m20 : M 2 0 = 0 := by linear_combination F4.ω * f40 - g40 + (F4.ω ^ 2 - F4.ω) * h04
  have m42 : M 4 2 = 0 := by linear_combination (1 + F4.ω) * f40 - g40 + F4.ω ^ 2 * h04
  have m23 : M 2 3 = 0 := by linear_combination f43
  have m44 : M 4 4 = M 0 0 := h04.symm
  fin_cases i <;> fin_cases j <;> simp <;> assumption

theorem mem_ZX₄sub_of_comm_A₁ {g : SU52} (h : ∀ a ∈ A₁sub, g * a = a * g) : g ∈ ZX₄sub := by
  have hc : ∀ {a : SU52}, a ∈ A₁sub → mat g * mat a = mat a * mat g := fun ha => by
    rw [← mat_mul, ← mat_mul, h _ ha]
  have ez : mat g * x₄Mat 0 1 = x₄Mat 0 1 * mat g := by
    rw [← mat_zSU]
    exact hc (X₄sub_le_A₁sub' (ZX₄sub_le_X₄sub zSU_mem))
  have e₂ : mat g * x₂Mat 1 = x₂Mat 1 * mat g := by
    rw [← mat_x₂SU]
    exact hc (X₂sub_le_A₁sub (x₂SU_mem 1))
  have e₂' : mat g * x₂Mat F4.ω = x₂Mat F4.ω * mat g := by
    rw [← mat_x₂SU]
    exact hc (X₂sub_le_A₁sub (x₂SU_mem F4.ω))
  have e₃ : mat g * x₃Mat 1 = x₃Mat 1 * mat g := by
    rw [← mat_x₃SU]
    exact hc (X₃sub_le_A₁sub (x₃SU_mem 1))
  have e₃' : mat g * x₃Mat F4.ω = x₃Mat F4.ω * mat g := by
    rw [← mat_x₃SU]
    exact hc (X₃sub_le_A₁sub (x₃SU_mem F4.ω))
  have e₄ : mat g * x₄Mat 1 F4.ω = x₄Mat 1 F4.ω * mat g := by
    rw [← mat_x₄SU 1 F4.ω one_omega_rel]
    exact hc (X₄sub_le_A₁sub' (mem_X₄sub.2 ⟨1, F4.ω, mat_x₄SU _ _ _⟩))
  have e₄' : mat g * x₄Mat F4.ω F4.ω = x₄Mat F4.ω F4.ω * mat g := by
    rw [← mat_x₄SU F4.ω F4.ω omega_omega_rel]
    exact hc (X₄sub_le_A₁sub' (mem_X₄sub.2 ⟨F4.ω, F4.ω, mat_x₄SU _ _ _⟩))
  have hform := eq_of_comm_A₁_gens ez e₂ e₂' e₃ e₃' e₄ e₄'
  have hlt : (mat g).IsLowerTriangular := fun i j hij => by
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    have h40 : ¬ (i = 4 ∧ j = 0) := by
      rintro ⟨rfl, rfl⟩
      exact absurd hij' (by decide)
    rw [hform i j]
    simp [ne_of_lt hij', h40]
  have hd : ∀ i : Fin 5, mat g i i = mat g 0 0 := fun i => by rw [hform i i]; simp
  have hdet := Matrix.det_of_isLowerTriangular (mat g) hlt
  rw [(mem_SU52.1 g.2).2, Fin.prod_univ_five, hd 1, hd 2, hd 3, hd 4] at hdet
  have h1 : mat g 0 0 = 1 := eq_one_of_pow_five _ (by rw [hdet]; ring)
  refine mem_x₄Sub.2 ⟨0, mat g 4 0, rfl, ?_⟩
  ext i j
  rw [hform i j, h1]
  fin_cases i <;> fin_cases j <;> simp [x₄Mat]

theorem not_conj_fld_fix (s : SU52) : ¬ ∀ a ∈ A₁sub, s * fld a * s⁻¹ = a := by
  intro h
  have hz := h zSU (X₄sub_le_A₁sub' (ZX₄sub_le_X₄sub zSU_mem))
  rw [fld_zSU] at hz
  have hz' : s * zSU = zSU * s := by
    calc s * zSU = s * zSU * s⁻¹ * s := by group
      _ = zSU * s := by rw [hz]
  obtain ⟨⟨h0, -⟩, -⟩ := isBlk_of_comm_z hz'
  have e1 := h (x₂SU 1) (X₂sub_le_A₁sub (x₂SU_mem 1))
  have eω := h (x₂SU F4.ω) (X₂sub_le_A₁sub (x₂SU_mem F4.ω))
  rw [fld_x₂SU] at e1 eω
  have k1 : mat s * x₂Mat (bar 1) = x₂Mat 1 * mat s := by
    have : s * x₂SU (bar 1) = x₂SU 1 * s := by
      calc s * x₂SU (bar 1) = s * x₂SU (bar 1) * s⁻¹ * s := by group
        _ = x₂SU 1 * s := by rw [e1]
    rw [← mat_x₂SU, ← mat_x₂SU, ← mat_mul, ← mat_mul, this]
  have kω : mat s * x₂Mat (bar F4.ω) = x₂Mat F4.ω * mat s := by
    have : s * x₂SU (bar F4.ω) = x₂SU F4.ω * s := by
      calc s * x₂SU (bar F4.ω) = s * x₂SU (bar F4.ω) * s⁻¹ * s := by group
        _ = x₂SU F4.ω * s := by rw [eω]
    rw [← mat_x₂SU, ← mat_x₂SU, ← mat_mul, ← mat_mul, this]
  have a := congrFun (congrFun k1 1) 0
  have b := congrFun (congrFun kω 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_five, x₂Mat, bar_ω] at a b
  have s00 : mat s 0 0 = 0 := by linear_combination b - (F4.ω + 1) * a
  have hrow : ∀ j, mat s 0 j = 0 := fun j => by
    by_cases hj : j = 0
    · rw [hj, s00]
    · exact h0 j hj
  have hdet := (mem_SU52.1 s.2).2
  rw [Matrix.det_succ_row_zero] at hdet
  simp [hrow] at hdet

@[expose] def ι3 : Fin 3 → Fin 5 := ![1, 2, 3]

@[expose] def blk3 (M : Matrix (Fin 5) (Fin 5) F4) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun i j => M (ι3 i) (ι3 j)

theorem blk3_mul {M M' : Matrix (Fin 5) (Fin 5) F4} (hM : IsBlk M) (hM' : IsBlk M') :
    blk3 (M * M') = blk3 M * blk3 M' := by
  have z1 := hM'.1 1 (by decide)
  have z2 := hM'.1 2 (by decide)
  have z3 := hM'.1 3 (by decide)
  have w1 := hM.2 1 (by decide)
  have w2 := hM.2 2 (by decide)
  have w3 := hM.2 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, ι3, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, z1, z2, z3, w1, w2, w3]

@[expose] def CzSub : Subgroup SU52 := centralizer {zSU}

theorem comm_of_mem_CzSub {g : SU52} (hg : g ∈ CzSub) : g * zSU = zSU * g :=
  mem_centralizer_singleton_iff.1 hg

@[expose] def leviMon : CzSub →* Matrix (Fin 3) (Fin 3) F4 where
  toFun g := blk3 (mat g)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' g g' := blk3_mul (isBlk_of_comm_z (comm_of_mem_CzSub g.2)).1
    (isBlk_of_comm_z (comm_of_mem_CzSub g'.2)).1

@[expose] def levi1 : CzSub →* GL (Fin 3) F4 := leviMon.toHomUnits

theorem coe_levi1 (g : CzSub) :
    ((levi1 g : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = blk3 (mat g) := rfl

theorem eq_one_of_sq : ∀ c : F4, c ^ 2 = 1 → c = 1 := by decide

theorem mem_A₁sub_of_levi1_eq_one {g : CzSub} (hg : levi1 g = 1) : (g : SU52) ∈ A₁sub := by
  have hB : blk3 (mat g) = 1 := by
    rw [← coe_levi1, hg]
    rfl
  obtain ⟨⟨h0, h4⟩, h04⟩ := isBlk_of_comm_z (comm_of_mem_CzSub g.2)
  have hb : ∀ i j : Fin 3, mat g (ι3 i) (ι3 j) = (1 : Matrix (Fin 3) (Fin 3) F4) i j :=
    fun i j => congrFun (congrFun hB i) j
  have r1 := h0 1 (by decide)
  have r2 := h0 2 (by decide)
  have r3 := h0 3 (by decide)
  have r4 := h0 4 (by decide)
  have c1 := h4 1 (by decide)
  have c2 := h4 2 (by decide)
  have c3 := h4 3 (by decide)
  have m11 : mat g 1 1 = 1 := by simpa [ι3] using hb 0 0
  have m12 : mat g 1 2 = 0 := by simpa [ι3] using hb 0 1
  have m13 : mat g 1 3 = 0 := by simpa [ι3] using hb 0 2
  have m21 : mat g 2 1 = 0 := by simpa [ι3] using hb 1 0
  have m22 : mat g 2 2 = 1 := by simpa [ι3] using hb 1 1
  have m23 : mat g 2 3 = 0 := by simpa [ι3] using hb 1 2
  have m31 : mat g 3 1 = 0 := by simpa [ι3] using hb 2 0
  have m32 : mat g 3 2 = 0 := by simpa [ι3] using hb 2 1
  have m33 : mat g 3 3 = 1 := by simpa [ι3] using hb 2 2
  have hlt : (mat g).IsLowerTriangular := fun i j hij => by
    have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
    fin_cases i <;> fin_cases j <;> simp [r1, r2, r3, r4, c1, c2, c3, m12, m13, m23] at hij' ⊢
  have hdet := Matrix.det_of_isLowerTriangular (mat g) hlt
  rw [(mem_SU52.1 (g : SU52).2).2, Fin.prod_univ_five, m11, m22, m33, ← h04] at hdet
  have hl : mat g 0 0 = 1 := eq_one_of_sq _ (by rw [hdet]; ring)
  have hl4 : mat g 4 4 = 1 := h04 ▸ hl
  refine mem_A₁sub_of_shape fun i j hij => ?_
  rw [Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp [r1, r2, r3, r4, c1, c2, c3, m11, m12, m13, m21, m22, m23, m31, m32, m33, hl, hl4]
      at hij ⊢

@[expose] def J3 : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun i j => if i.val + j.val = 2 then 1 else 0

@[expose] def GU3 : Subgroup (GL (Fin 3) F4) where
  carrier := {g | ((g : Matrix (Fin 3) (Fin 3) F4).map hF4.bar)ᵀ * J3 * g = J3}
  mul_mem' {g g'} hg hg' := by
    change (((g * g' : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).map hF4.bar)ᵀ * J3 *
      ((g * g' : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = J3
    rw [Units.val_mul, conjTranspose_mul_mul, hg]
    exact hg'
  one_mem' := by
    change (((1 : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).map hF4.bar)ᵀ * J3 *
      ((1 : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = J3
    simp
  inv_mem' {g} hg := by
    have hgg : (g : Matrix (Fin 3) (Fin 3) F4) *
        ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 := conjTranspose_mul_mul hF4 J3 (g : Matrix (Fin 3) (Fin 3) F4)
      ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
    change ((g : Matrix (Fin 3) (Fin 3) F4).map hF4.bar)ᵀ * J3 *
      (g : Matrix (Fin 3) (Fin 3) F4) = J3 at hg
    rw [hg, hgg] at h1
    simp only [Matrix.map_one _ (map_zero hF4.bar) (map_one hF4.bar), transpose_one,
      Matrix.one_mul, Matrix.mul_one] at h1
    exact h1.symm

theorem toLin_mem_GU3_iff (g : GL (Fin 3) F4) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (gramForm hF4 J3) ↔ g ∈ GU3 := by
  rw [mem_sesqUnitaryGroup]
  change _ ↔ ((g : Matrix (Fin 3) (Fin 3) F4).map hF4.bar)ᵀ * J3 * g = J3
  rw [← gramForm_isometry_iff]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply', Matrix.toLin'_apply]

theorem card_GU3 : Nat.card GU3 = 648 := by
  have hJ : (J3.map hF4.bar)ᵀ = J3 := by
    rw [hF4_bar]
    decide
  have hdet : J3.det ≠ 0 := by
    rw [Matrix.det_fin_three]
    decide
  have hn : Module.finrank F4 (Fin 3 → F4) = 3 := by simp
  have hU := (CFSG.LinearGroups.unitary_full_group_order hF4 (gramForm_isSymm hF4 hJ)
    (gramForm_separatingLeft hF4 hdet) hn (by norm_num)).1
  have e : Nat.card GU3 = Nat.card (sesqUnitaryGroup (gramForm hF4 J3)) :=
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g =>
      (toLin_mem_GU3_iff g).symm)
  have : (Nat.card GU3 : ℤ) = 648 := by
    rw [e, hU]
    decide
  exact_mod_cast this

theorem levi1_mem_GU3 (g : CzSub) : levi1 g ∈ GU3 := by
  obtain ⟨⟨h0, -⟩, -⟩ := isBlk_of_comm_z (comm_of_mem_CzSub g.2)
  have hU := (mem_SU52.1 (g : SU52).2).1
  have r1 := h0 1 (by decide)
  have r2 := h0 2 (by decide)
  have r3 := h0 3 (by decide)
  change ((blk3 (mat g)).map hF4.bar)ᵀ * J3 * blk3 (mat g) = J3
  rw [hF4_bar]
  ext i j
  have e := congrFun (congrFun hU (ι3 i)) (ι3 j)
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, J5, J3, blk3, ι3, r1, r2,
      r3] at e ⊢ <;> linear_combination e

theorem card_CzSub_dvd : Nat.card CzSub ∣ 2 ^ 7 * 648 := by
  have h1 := levi1.ker.card_mul_index
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  refine Nat.mul_dvd_mul ?_ ?_
  · have hle : levi1.ker.map CzSub.subtype ≤ A₁sub := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_A₁sub_of_levi1_eq_one hx
    rw [← Subgroup.card_map_of_injective CzSub.subtype_injective, ← card_A₁sub]
    exact Subgroup.card_dvd_of_le hle
  · rw [← card_GU3]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨g, rfl⟩
    exact levi1_mem_GU3 g

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
