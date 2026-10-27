module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks

public section

namespace CFSG.SectionRank.QTK

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven
open CFSG.RankThree.PartTwo.Census (threeCycleMat threeCycleMat_pow_three threeCycleMat_pow_val_add
  threeCycleMat_pow_val_zero_one det_threeCycleMat eq_one_of_mul_self_eq_one isElemAbelian_range
  le_localRank_quotient_of_le_normalizer le_normalizer_of_conj_mem pslReindex
  localRank_eq_of_mulEquiv)

variable {K : Type} [Field K] [CharP K 2]

@[expose] def sBlockMat3 (a : Fin 3 → ZMod 3) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K :=
  blockDiagonal fun b => threeCycleMat K ^ (a b).val

theorem sBlockMat3_add (a a' : Fin 3 → ZMod 3) :
    sBlockMat3 (K := K) (a + a') = sBlockMat3 a * sBlockMat3 a' := by
  rw [sBlockMat3, sBlockMat3, sBlockMat3, ← blockDiagonal_mul]
  congr 1
  funext b
  rw [Pi.add_apply, threeCycleMat_pow_val_add]

theorem det_sBlockMat3 (a : Fin 3 → ZMod 3) : (sBlockMat3 (K := K) a).det = 1 := by
  rw [sBlockMat3, det_blockDiagonal]
  exact Finset.prod_eq_one fun b _ => by rw [det_pow, det_threeCycleMat, one_pow]

abbrev BlockIdx3 (m : ℕ) : Type := (Fin 2 × Fin 3) ⊕ Fin m

@[expose] def sHom3 (m : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Fin 3 → ZMod 3) →* SpecialLinearGroup (BlockIdx3 m) K where
  toFun a := ⟨fromBlocks (sBlockMat3 a.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_sBlockMat3, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (sBlockMat3 (0 : Fin 3 → ZMod 3)) 0 0 1 = (1 : Matrix (BlockIdx3 m) _ K)
    rw [← fromBlocks_one, sBlockMat3]
    congr 1
    rw [← blockDiagonal_one]
    congr 1)
  map_mul' a b := Subtype.ext (by
    change fromBlocks (sBlockMat3 (a.toAdd + b.toAdd)) 0 0 1 =
      fromBlocks (sBlockMat3 (K := K) a.toAdd) 0 0 1 * fromBlocks (sBlockMat3 b.toAdd) 0 0 1
    rw [fromBlocks_multiply, sBlockMat3_add]
    simp)

theorem coe_sHom3 (m : ℕ) (a : Multiplicative (Fin 3 → ZMod 3)) :
    ((sHom3 m K a : SpecialLinearGroup (BlockIdx3 m) K) : Matrix (BlockIdx3 m) (BlockIdx3 m) K) =
      fromBlocks (sBlockMat3 a.toAdd) 0 0 1 :=
  rfl

@[expose] def yMat3 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K :=
  Matrix.of fun ib jb => if ib.2 = 0 ∧ jb.2 = 1 then X ib.1 jb.1 else 0

omit [CharP K 2] in
theorem yMat3_mul_yMat3 (X X' : Matrix (Fin 2) (Fin 2) K) : yMat3 X * yMat3 X' = 0 := by
  ext ib jb
  simp only [mul_apply, yMat3, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun kc _ => ?_
  by_cases h : kc.2 = 1
  · have : ¬ (kc.2 = 0 ∧ jb.2 = 1) := fun h' => by rw [h] at h'; exact absurd h'.1 (by decide)
    rw [ite_eq_right this, mul_zero]
  · have : ¬ (ib.2 = 0 ∧ kc.2 = 1) := fun h' => h h'.2
    rw [ite_eq_right this, zero_mul]

omit [CharP K 2] in
theorem yMat3_zero : yMat3 (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext ib jb
  simp [yMat3]

omit [CharP K 2] in
theorem yMat3_add (X X' : Matrix (Fin 2) (Fin 2) K) : yMat3 (X + X') = yMat3 X + yMat3 X' := by
  ext ib jb
  simp only [yMat3, of_apply, Matrix.add_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem one_add_yMat3_mul (X X' : Matrix (Fin 2) (Fin 2) K) :
    (1 + yMat3 X) * (1 + yMat3 X') = 1 + yMat3 (X + X') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, yMat3_mul_yMat3, add_zero, yMat3_add]
  abel

theorem det_one_add_yMat3 (X : Matrix (Fin 2) (Fin 2) K) : (1 + yMat3 X).det = 1 := by
  have hX : X + X = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  refine eq_one_of_mul_self_eq_one ?_
  rw [← det_mul, one_add_yMat3_mul, hX, yMat3_zero, add_zero, det_one]

@[expose] def uHom3 (m : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Matrix (Fin 2) (Fin 2) K) →* SpecialLinearGroup (BlockIdx3 m) K where
  toFun X := ⟨fromBlocks (1 + yMat3 X.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_one_add_yMat3, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (1 + yMat3 (0 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
      (1 : Matrix (BlockIdx3 m) _ K)
    rw [← fromBlocks_one, yMat3_zero, add_zero])
  map_mul' X X' := Subtype.ext (by
    change fromBlocks (1 + yMat3 (X.toAdd + X'.toAdd)) 0 0 1 =
      fromBlocks (1 + yMat3 (K := K) X.toAdd) 0 0 1 * fromBlocks (1 + yMat3 X'.toAdd) 0 0 1
    rw [fromBlocks_multiply, one_add_yMat3_mul]
    simp)

theorem sBlockMat3_mul_yMat3 (a : Fin 3 → ZMod 3) (X : Matrix (Fin 2) (Fin 2) K) :
    sBlockMat3 a * yMat3 X =
      yMat3 (threeCycleMat K ^ (a 0).val * X * threeCycleMat K ^ (-(a 1)).val) * sBlockMat3 a := by
  set X' := threeCycleMat K ^ (a 0).val * X * threeCycleMat K ^ (-(a 1)).val with hX'
  have key : threeCycleMat K ^ (a 0).val * X = X' * threeCycleMat K ^ (a 1).val := by
    rw [hX', mul_assoc _ (threeCycleMat K ^ (-(a 1)).val), ← threeCycleMat_pow_val_add,
      show -(a 1) + a 1 = 0 from neg_add_cancel _, ZMod.val_zero, pow_zero, mul_one]
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp only [mul_apply, Fintype.sum_prod_type, sBlockMat3, blockDiagonal_apply, yMat3, of_apply]
  by_cases h : b = 0 ∧ b' = 1
  · obtain ⟨rfl, rfl⟩ := h
    have := congrFun (congrFun key i) j
    simp only [mul_apply] at this
    simpa [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
  · have h1 : ∀ k c, (if b = c then (threeCycleMat K ^ (a b).val) i k else 0) *
        (if c = 0 ∧ b' = 1 then X k j else 0) = 0 := by
      intro k c
      by_cases hbc : b = c
      · subst hbc
        rw [ite_eq_right h, mul_zero]
      · rw [ite_eq_right hbc, zero_mul]
    have h2 : ∀ k c, (if b = 0 ∧ c = 1 then X' i k else 0) *
        (if c = b' then (threeCycleMat K ^ (a c).val) k j else 0) = 0 := by
      intro k c
      by_cases hc : c = b'
      · subst hc
        rw [ite_eq_right h, zero_mul]
      · rw [ite_eq_right hc, mul_zero]
    simp only [h1, h2, Finset.sum_const_zero]

theorem eq_one_of_sHom3_entry {m : ℕ} {a : Multiplicative (Fin 3 → ZMod 3)}
    (h : ∀ b : Fin 3, ((sHom3 m K a : SpecialLinearGroup (BlockIdx3 m) K) :
      Matrix (BlockIdx3 m) (BlockIdx3 m) K) (.inl (0, b)) (.inl (1, b)) = 0) : a = 1 := by
  apply Multiplicative.toAdd.injective
  funext b
  have hb := h b
  rw [coe_sHom3, fromBlocks_apply₁₁, sBlockMat3, blockDiagonal_apply] at hb
  simp only [ite_true] at hb
  exact threeCycleMat_pow_val_zero_one hb

theorem three_le_localRank_PSL_blocks3 [Finite K] (m : ℕ) :
    3 ≤ localRank 3 (ProjectiveSpecialLinearGroup (BlockIdx3 m) K) := by
  set φ := sHom3 m K
  set ψ := uHom3 m K
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun a ha =>
      eq_one_of_sHom3_entry (K := K) (m := m) fun b => ?_
    rw [ha]
    simp
  refine le_localRank_quotient_of_le_normalizer _ Nat.prime_three (E := φ.range) (P := ψ.range)
    (isElemAbelian_range (fun a => ?_) φ) ?_ ?_ ?_ ?_ ?_
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext b
    change 3 • (Multiplicative.toAdd a b) = 0
    generalize Multiplicative.toAdd a b = x
    revert x
    decide
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, hxc⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have ha : a = 1 := eq_one_of_sHom3_entry (K := K) (m := m) fun b => by
      rw [← hc]
      simp
    rw [Subgroup.mem_bot, ha, map_one]
  · intro y
    obtain ⟨X, hX⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hX, ← map_mul, OneMemClass.coe_one]
    have hXX : X * X = 1 := by
      apply Multiplicative.toAdd.injective
      ext i j
      simp only [toAdd_mul, toAdd_one, Matrix.add_apply, Matrix.zero_apply,
        CharTwo.add_self_eq_zero]
    rw [hXX, map_one]
  · intro hP
    have h1 : ψ (Multiplicative.ofAdd 1) ∈ ψ.range := ⟨_, rfl⟩
    obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hP h1)
    have : (scalar (BlockIdx3 m) c) (.inl (0, 0)) (.inl (0, 1)) =
        (fromBlocks (1 + yMat3 (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 :
          Matrix (BlockIdx3 m) (BlockIdx3 m) K) (.inl (0, 0)) (.inl (0, 1)) := by
      rw [hc]
      rfl
    simp [yMat3, scalar_apply] at this
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨a, rfl⟩ _ ⟨X, rfl⟩
    refine ⟨Multiplicative.ofAdd (threeCycleMat K ^ (a.toAdd 0).val * X.toAdd *
      threeCycleMat K ^ (-(a.toAdd 1)).val), ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Subtype.ext ?_
    change fromBlocks (1 + yMat3 _) 0 0 1 * fromBlocks (sBlockMat3 a.toAdd) 0 0 1 =
      fromBlocks (sBlockMat3 a.toAdd) 0 0 1 * fromBlocks (1 + yMat3 X.toAdd) 0 0 1
    rw [fromBlocks_multiply, fromBlocks_multiply, mul_add, add_mul, sBlockMat3_mul_yMat3]
    simp

theorem three_le_localRank_PSL_of_six_le [Finite K] {n : ℕ} (hn : 6 ≤ n) :
    3 ≤ localRank 3 (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hcard : Fintype.card (BlockIdx3 (n - 6)) = n := by
    simp only [BlockIdx3, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  rw [← localRank_eq_of_mulEquiv (pslReindex K (Fintype.equivFinOfCardEq hcard)) Nat.prime_three]
  exact three_le_localRank_PSL_blocks3 (n - 6)

end CFSG.SectionRank.QTK
