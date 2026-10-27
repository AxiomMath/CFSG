module

public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LinearGroups
open scoped MatrixGroups commutatorElement

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

abbrev SLm2 := SpecialLinearGroup (Fin (m+2)) F

abbrev SLm1 := SpecialLinearGroup (Fin (m+1)) F

@[expose] def rowRadical (a : Fin (m+2)) : Subgroup (SLm2 m F) where
  carrier := {g | (g : Matrix (Fin (m+2)) (Fin (m+2)) F) a a = 1 ∧
    ∀ i j, i ≠ a → (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i j =
      (1 : Matrix (Fin (m+2)) (Fin (m+2)) F) i j}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
    · intro i j _
      rw [Matrix.SpecialLinearGroup.coe_one]
  mul_mem' := by
    intro g h hg hh
    refine ⟨?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Finset.sum_eq_single a]
      · simp [hg.1, hh.1]
      · intro x _ hxa
        rw [hh.2 x a hxa, Matrix.one_apply_ne hxa, mul_zero]
      · simp
    · intro i j hi
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Finset.sum_eq_single i]
      · simp [hg.2 i i hi, hh.2 i j hi]
      · intro x _ hxi
        rw [hg.2 i x hi, Matrix.one_apply_ne (Ne.symm hxi), zero_mul]
      · simp
  inv_mem' := by
    intro g hg
    have hrow : ∀ i j, i ≠ a →
        ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) i j =
          (1 : Matrix (Fin (m+2)) (Fin (m+2)) F) i j := by
      intro i j hi
      have hone := congrArg (fun x : SLm2 m F =>
          (x : Matrix (Fin (m+2)) (Fin (m+2)) F) i j) (mul_inv_cancel g)
      have hsum : (∑ x : Fin (m+2),
          (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i x *
            ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) x j) =
          (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i i *
            ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) i j := by
        rw [Finset.sum_eq_single i]
        · intro x _ hxi
          rw [hg.2 i x hi, Matrix.one_apply_ne (Ne.symm hxi), zero_mul]
        · intro hi'; simp at hi'
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, hsum,
        hg.2 i i hi, Matrix.one_apply_eq] at hone
      simpa using hone
    refine ⟨?_, hrow⟩
    have hone := congrArg (fun x : SLm2 m F =>
        (x : Matrix (Fin (m+2)) (Fin (m+2)) F) a a) (mul_inv_cancel g)
    have hsum : (∑ x : Fin (m+2),
        (g : Matrix (Fin (m+2)) (Fin (m+2)) F) a x *
          ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) x a) =
        (g : Matrix (Fin (m+2)) (Fin (m+2)) F) a a *
          ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) a a := by
      rw [Finset.sum_eq_single a]
      · intro x _ hxa
        rw [hrow x a hxa, Matrix.one_apply_ne hxa, mul_zero]
      · intro ha; simp at ha
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, hsum, hg.1] at hone
    simpa [Matrix.one_apply_eq] using hone

@[expose] def colRadical (b : Fin (m+2)) : Subgroup (SLm2 m F) where
  carrier := {g | (g : Matrix (Fin (m+2)) (Fin (m+2)) F) b b = 1 ∧
    ∀ i j, j ≠ b → (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i j =
      (1 : Matrix (Fin (m+2)) (Fin (m+2)) F) i j}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
    · intro i j _
      rw [Matrix.SpecialLinearGroup.coe_one]
  mul_mem' := by
    intro g h hg hh
    refine ⟨?_, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Finset.sum_eq_single b]
      · simp [hg.1, hh.1]
      · intro x _ hxb
        rw [hg.2 b x hxb, Matrix.one_apply_ne (Ne.symm hxb), zero_mul]
      · simp
    · intro i j hb
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Finset.sum_eq_single j]
      · simp [hg.2 i j hb, hh.2 j j hb]
      · intro x _ hxj
        rw [hh.2 x j hb, Matrix.one_apply_ne hxj, mul_zero]
      · simp
  inv_mem' := by
    intro g hg
    have hcol : ∀ i j, j ≠ b →
        ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) i j =
          (1 : Matrix (Fin (m+2)) (Fin (m+2)) F) i j := by
      intro i j hb
      have hone := congrArg (fun x : SLm2 m F =>
          (x : Matrix (Fin (m+2)) (Fin (m+2)) F) i j) (inv_mul_cancel g)
      have hsum : (∑ x : Fin (m+2),
          ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) i x *
            (g : Matrix (Fin (m+2)) (Fin (m+2)) F) x j) =
          ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) i j *
            (g : Matrix (Fin (m+2)) (Fin (m+2)) F) j j := by
        rw [Finset.sum_eq_single j]
        · intro x _ hxj
          rw [hg.2 x j hb, Matrix.one_apply_ne hxj, mul_zero]
        · intro hj'; simp at hj'
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, hsum,
        hg.2 j j hb, Matrix.one_apply_eq] at hone
      simpa using hone
    refine ⟨?_, hcol⟩
    have hone := congrArg (fun x : SLm2 m F =>
        (x : Matrix (Fin (m+2)) (Fin (m+2)) F) b b) (mul_inv_cancel g)
    have hsum : (∑ x : Fin (m+2),
        (g : Matrix (Fin (m+2)) (Fin (m+2)) F) b x *
          ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) x b) =
        (g : Matrix (Fin (m+2)) (Fin (m+2)) F) b b *
          ((g⁻¹ : SLm2 m F) : Matrix (Fin (m+2)) (Fin (m+2)) F) b b := by
      rw [Finset.sum_eq_single b]
      · intro x _ hxb
        rw [hg.2 b x hxb, Matrix.one_apply_ne (Ne.symm hxb), zero_mul]
      · intro hb'; simp at hb'
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, hsum, hg.1] at hone
    simpa [Matrix.one_apply_eq] using hone

abbrev firstRowRadical : Subgroup (SLm2 m F) := rowRadical m F 0

abbrev firstColRadical : Subgroup (SLm2 m F) := colRadical m F 0

abbrev lastColRadical : Subgroup (SLm2 m F) := colRadical m F (Fin.last (m+1))

abbrev lastRowRadical : Subgroup (SLm2 m F) := rowRadical m F (Fin.last (m+1))

omit [Finite F] in
theorem mem_rowRadical {a : Fin (m+2)} {g : SLm2 m F} :
    g ∈ rowRadical m F a ↔
      (g : Matrix (Fin (m+2)) (Fin (m+2)) F) a a = 1 ∧
        ∀ i j, i ≠ a → (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i j =
          (1 : Matrix (Fin (m+2)) (Fin (m+2)) F) i j :=
  Iff.rfl

omit [Finite F] in
theorem mem_colRadical {b : Fin (m+2)} {g : SLm2 m F} :
    g ∈ colRadical m F b ↔
      (g : Matrix (Fin (m+2)) (Fin (m+2)) F) b b = 1 ∧
        ∀ i j, j ≠ b → (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i j =
          (1 : Matrix (Fin (m+2)) (Fin (m+2)) F) i j :=
  Iff.rfl

omit [Fact (Nat.Prime p)] in
theorem firstRowRadical_le_U :
    firstRowRadical m F ≤ (curtisDatum (m+1) F p).U := by
  intro g hg
  rw [mem_curtisDatum_U_iff]
  constructor
  · intro i
    by_cases hi : i = 0
    · subst hi
      exact hg.1
    · rw [hg.2 i i hi, Matrix.one_apply_eq]
  · intro i j hji
    have hi : i ≠ 0 := by
      intro h
      subst h
      exact (not_lt_of_ge (Fin.zero_le j)) hji
    rw [hg.2 i j hi]
    exact Matrix.one_apply_ne (by omega)

omit [Fact (Nat.Prime p)] in
theorem firstColRadical_le_L :
    firstColRadical m F ≤ (curtisDatum (m+1) F p).L := by
  intro g hg
  rw [mem_curtisDatum_L_iff]
  constructor
  · intro i
    by_cases hi : i = 0
    · subst hi
      exact hg.1
    · rw [hg.2 i i hi, Matrix.one_apply_eq]
  · intro i j hij
    have hj : j ≠ 0 := by
      intro h
      subst h
      exact (not_lt_of_ge (Fin.zero_le i)) hij
    rw [hg.2 i j hj]
    exact Matrix.one_apply_ne (by omega)

omit [Fact (Nat.Prime p)] in
theorem lastColRadical_le_U :
    lastColRadical m F ≤ (curtisDatum (m+1) F p).U := by
  intro g hg
  rw [mem_curtisDatum_U_iff]
  constructor
  · intro i
    by_cases hi : i = Fin.last (m+1)
    · subst hi
      exact hg.1
    · rw [hg.2 i i hi, Matrix.one_apply_eq]
  · intro i j hji
    have hj : j ≠ Fin.last (m+1) := by
      intro h
      subst h
      exact (not_lt_of_ge (Fin.le_last i)) hji
    rw [hg.2 i j hj]
    exact Matrix.one_apply_ne (by omega)

omit [Fact (Nat.Prime p)] in
theorem lastRowRadical_le_L :
    lastRowRadical m F ≤ (curtisDatum (m+1) F p).L := by
  intro g hg
  rw [mem_curtisDatum_L_iff]
  constructor
  · intro i
    by_cases hi : i = Fin.last (m+1)
    · subst hi
      exact hg.1
    · rw [hg.2 i i hi, Matrix.one_apply_eq]
  · intro i j hij
    have hi : i ≠ Fin.last (m+1) := by
      intro h
      subst h
      exact (not_lt_of_ge (Fin.le_last j)) hij
    rw [hg.2 i j hi]
    exact Matrix.one_apply_ne (by omega)

end

end CFSG.LieType.SpecialLinear
