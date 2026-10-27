module

public import CFSG.CGT.T75JM.N6Branch
public import CFSG.CGT.T75JM.N6Sem

public section

namespace CFSG.CGT.T75JM

variable {G : Type*} [Group G] {T : Subgroup G} (c : Coords T)

theorem tOf_mul {u w : ℕ} (hu : u < 16) (hw : w < 16) :
    tOf c (u ^^^ w) = tOf c u * tOf c w := by
  apply c.inj
  rw [c.mul, coord_tOf c hu, coord_tOf c hw, coord_tOf c (Nat.xor_lt_two_pow (n := 4) hu hw)]

theorem modelX_lt : ∀ i, modelX.col i < 16 := by decide
theorem modelY_lt : ∀ i, modelY.col i < 16 := by decide

theorem ctr_tOf (g : Subgroup.normalizer (T : Set G)) (M : Cols) (hM : colsOf c g = M)
    (hlt : ∀ i, M.col i < 16) (i : Fin 4) :
    ctr g (tOf c (2 ^ i.val)) = tOf c (M.col i) := by
  apply c.inj
  have h2 : 2 ^ i.val < 16 := by fin_cases i <;> decide
  rw [coord_ctr, hM, coord_tOf c h2, coord_tOf c (hlt i), applyC_basis]

@[expose] def inN (t : T) : Subgroup.normalizer (T : Set G) :=
  ⟨(t : G), Subgroup.le_normalizer t.2⟩

@[expose] noncomputable def tN (i : ℕ) : Subgroup.normalizer (T : Set G) := inN (tOf c (2 ^ i))

theorem act_coe (g : Subgroup.normalizer (T : Set G)) (t : T) :
    ((g * inN t * g⁻¹ : Subgroup.normalizer (T : Set G)) : G) = ((ctr g t : T) : G) := by
  simp [inN, ctr]

theorem act_eq (g : Subgroup.normalizer (T : Set G)) (M : Cols) (hM : colsOf c g = M)
    (hlt : ∀ i, M.col i < 16) (i : Fin 4) :
    g * tN c i.val * g⁻¹ = inN (tOf c (M.col i)) := by
  apply Subtype.ext
  rw [show tN c i.val = inN (tOf c (2 ^ i.val)) from rfl, act_coe, ctr_tOf c g M hM hlt i]
  rfl

theorem inN_mul (a b : T) : inN a * inN b = (inN (a * b) : Subgroup.normalizer (T : Set G)) :=
  rfl

include c in
theorem inN_sq (a : T) : inN a * inN a = (1 : Subgroup.normalizer (T : Set G)) := by
  rw [inN_mul, coord_sq c]; rfl

include c in
theorem inN_comm (a b : T) : inN a * inN b = (inN b * inN a : Subgroup.normalizer (T : Set G)) := by
  rw [inN_mul, inN_mul, mul_comm_T c]

theorem tOf_11 : tOf c 11 = tOf c 1 * tOf c 2 * tOf c 8 := by
  rw [show (11 : ℕ) = (1 ^^^ 2) ^^^ 8 by decide, tOf_mul c (by decide) (by decide),
    tOf_mul c (by decide) (by decide)]

theorem tOf_12 : tOf c 12 = tOf c 4 * tOf c 8 := by
  rw [show (12 : ℕ) = 4 ^^^ 8 by decide, tOf_mul c (by decide) (by decide)]

theorem tOf_10 : tOf c 10 = tOf c 2 * tOf c 8 := by
  rw [show (10 : ℕ) = 2 ^^^ 8 by decide, tOf_mul c (by decide) (by decide)]

theorem tOf_5 : tOf c 5 = tOf c 1 * tOf c 4 := by
  rw [show (5 : ℕ) = 1 ^^^ 4 by decide, tOf_mul c (by decide) (by decide)]

theorem tOf_9 : tOf c 9 = tOf c 1 * tOf c 8 := by
  rw [show (9 : ℕ) = 1 ^^^ 8 by decide, tOf_mul c (by decide) (by decide)]

theorem tN_0 : tN c 0 = inN (tOf c 1) := rfl
theorem tN_1 : tN c 1 = inN (tOf c 2) := rfl
theorem tN_2 : tN c 2 = inN (tOf c 4) := rfl
theorem tN_3 : tN c 3 = inN (tOf c 8) := rfl

theorem sem6_of_data (g h : Subgroup.normalizer (T : Set G)) (hg : colsOf c g = modelX)
    (hh : colsOf c h = modelY) (r1 : evalG g h wordR1 = 1) (r2 : evalG g h wordR2 = 1)
    (r3 : evalG g h wordR3 = 1) (r4 : evalG g h wordR4 = 1) :
    Sem6 ![g, h, tN c 0, tN c 1, tN c 2, tN c 3] := by
  obtain ⟨e1, e2, e3, e4⟩ := evalG_wordR g h
  rw [e1] at r1; rw [e2] at r2; rw [e3] at r3; rw [e4] at r4
  have ax := act_eq c g modelX hg modelX_lt
  have ay := act_eq c h modelY hh modelY_lt
  refine ⟨r1, ?_, r3, ?_, inN_sq c _, inN_sq c _, inN_sq c _, inN_sq c _, inN_comm c _ _,
    inN_comm c _ _, inN_comm c _ _, inN_comm c _ _, inN_comm c _ _, inN_comm c _ _, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · show h * h * h * h = 1
    simpa [pow_succ, mul_assoc] using r2
  · show (g * h * h) ^ 5 = 1
    exact r4
  · show g * tN c 0 * g⁻¹ = tN c 0
    exact (ax 0).trans rfl
  · show g * tN c 1 * g⁻¹ = tN c 0 * tN c 1 * tN c 3
    refine (ax 1).trans ?_
    show inN (tOf c 11) = _
    rw [tOf_11 c, tN_0, tN_1, tN_3, ← inN_mul, ← inN_mul]
  · show g * tN c 2 * g⁻¹ = tN c 2 * tN c 3
    refine (ax 2).trans ?_
    show inN (tOf c 12) = _
    rw [tOf_12 c, tN_2, tN_3, ← inN_mul]
  · show g * tN c 3 * g⁻¹ = tN c 3
    exact (ax 3).trans rfl
  · show h * tN c 0 * h⁻¹ = tN c 1 * tN c 3
    refine (ay 0).trans ?_
    show inN (tOf c 10) = _
    rw [tOf_10 c, tN_1, tN_3, ← inN_mul]
  · show h * tN c 1 * h⁻¹ = tN c 2
    exact (ay 1).trans rfl
  · show h * tN c 2 * h⁻¹ = tN c 0 * tN c 2
    refine (ay 2).trans ?_
    show inN (tOf c 5) = _
    rw [tOf_5 c, tN_0, tN_2, ← inN_mul]
  · show h * tN c 3 * h⁻¹ = tN c 0 * tN c 3
    refine (ay 3).trans ?_
    show inN (tOf c 9) = _
    rw [tOf_9 c, tN_0, tN_3, ← inN_mul]

end CFSG.CGT.T75JM
