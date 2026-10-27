module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
public import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open Matrix CFSG.Open

namespace LinFive

open Matrix

variable {K : Type} [Field K] [CharP K 2]

abbrev Idx (r : ℕ) : Type := (Fin 2 × Fin 5) ⊕ Fin r

private def sBlockMat (a : Fin 5 → ZMod 3) :
    Matrix (Fin 2 × Fin 5) (Fin 2 × Fin 5) K :=
  blockDiagonal fun b => CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a b).val

private theorem sBlockMat_add (a a' : Fin 5 → ZMod 3) :
    sBlockMat (K := K) (a + a') = sBlockMat a * sBlockMat a' := by
  rw [sBlockMat, sBlockMat, sBlockMat, ← blockDiagonal_mul]
  congr 1
  funext b
  rw [Pi.add_apply, CFSG.RankThree.PartTwo.Census.threeCycleMat_pow_val_add]

private theorem det_sBlockMat (a : Fin 5 → ZMod 3) : (sBlockMat (K := K) a).det = 1 := by
  rw [sBlockMat, det_blockDiagonal]
  exact Finset.prod_eq_one fun b _ => by
    rw [det_pow, CFSG.RankThree.PartTwo.Census.det_threeCycleMat, one_pow]

private def sHom (r : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Fin 5 → ZMod 3) →* SpecialLinearGroup (Idx r) K where
  toFun a := ⟨fromBlocks (sBlockMat a.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_sBlockMat, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (sBlockMat (0 : Fin 5 → ZMod 3)) 0 0 1 =
      (1 : Matrix (Idx r) (Idx r) K)
    rw [← fromBlocks_one, sBlockMat]
    congr 1
    rw [← blockDiagonal_one]
    congr 1)
  map_mul' a b := Subtype.ext (by
    change fromBlocks (sBlockMat (a.toAdd + b.toAdd)) 0 0 1 =
      fromBlocks (sBlockMat (K := K) a.toAdd) 0 0 1 * fromBlocks (sBlockMat b.toAdd) 0 0 1
    rw [fromBlocks_multiply, sBlockMat_add]
    simp)

private theorem coe_sHom (r : ℕ) (a : Multiplicative (Fin 5 → ZMod 3)) :
    ((sHom r K a : SpecialLinearGroup (Idx r) K) : Matrix (Idx r) (Idx r) K) =
      fromBlocks (sBlockMat a.toAdd) 0 0 1 := rfl

private def yMat (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2 × Fin 5) (Fin 2 × Fin 5) K :=
  Matrix.of fun ib jb => if ib.2 = 0 ∧ jb.2 = 1 then X ib.1 jb.1 else 0

private theorem yMat_mul_yMat (X X' : Matrix (Fin 2) (Fin 2) K) :
    yMat X * yMat X' = 0 := by
  ext ib jb
  simp only [mul_apply, yMat, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun kc _ => ?_
  by_cases h : kc.2 = 1
  · have : ¬ (kc.2 = 0 ∧ jb.2 = 1) := fun h' => by
      rw [h] at h'; exact absurd h'.1 (by decide)
    rw [ite_eq_right this, mul_zero]
  · have : ¬ (ib.2 = 0 ∧ kc.2 = 1) := fun h' => h h'.2
    rw [ite_eq_right this, zero_mul]

private theorem yMat_zero : yMat (0 : Matrix (Fin 2) (Fin 2) K) = 0 := by
  ext ib jb
  simp [yMat]

private theorem yMat_add (X X' : Matrix (Fin 2) (Fin 2) K) :
    yMat (X + X') = yMat X + yMat X' := by
  ext ib jb
  simp only [yMat, of_apply, Matrix.add_apply]
  split_ifs <;> simp

private theorem one_add_yMat_mul (X X' : Matrix (Fin 2) (Fin 2) K) :
    (1 + yMat X) * (1 + yMat X') = 1 + yMat (X + X') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, yMat_mul_yMat, add_zero, yMat_add]
  abel

private theorem det_one_add_yMat (X : Matrix (Fin 2) (Fin 2) K) :
    (1 + yMat X).det = 1 := by
  have hX : X + X = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
  refine CFSG.RankThree.PartTwo.Census.eq_one_of_mul_self_eq_one ?_
  rw [← det_mul, one_add_yMat_mul, hX, yMat_zero, add_zero, det_one]

private def uHom (r : ℕ) (K : Type) [Field K] [CharP K 2] :
    Multiplicative (Matrix (Fin 2) (Fin 2) K) →* SpecialLinearGroup (Idx r) K where
  toFun X := ⟨fromBlocks (1 + yMat X.toAdd) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, det_one_add_yMat, det_one, mul_one]⟩
  map_one' := Subtype.ext (by
    change fromBlocks (1 + yMat (0 : Matrix (Fin 2) (Fin 2) K)) 0 0 1 =
      (1 : Matrix (Idx r) (Idx r) K)
    rw [← fromBlocks_one, yMat_zero, add_zero])
  map_mul' X X' := Subtype.ext (by
    change fromBlocks (1 + yMat (X.toAdd + X'.toAdd)) 0 0 1 =
      fromBlocks (1 + yMat (K := K) X.toAdd) 0 0 1 * fromBlocks (1 + yMat X'.toAdd) 0 0 1
    rw [fromBlocks_multiply, one_add_yMat_mul]
    simp)

private theorem coe_uHom (r : ℕ) (X : Multiplicative (Matrix (Fin 2) (Fin 2) K)) :
    ((uHom r K X : SpecialLinearGroup (Idx r) K) : Matrix (Idx r) (Idx r) K) =
      fromBlocks (1 + yMat X.toAdd) 0 0 1 := rfl

private theorem sBlockMat_mul_yMat (a : Fin 5 → ZMod 3) (X : Matrix (Fin 2) (Fin 2) K) :
    sBlockMat a * yMat X =
      yMat (CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a 0).val * X *
        CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (-(a 1)).val) * sBlockMat a := by
  set X' := CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a 0).val * X *
    CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (-(a 1)).val with hX'
  have key : CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a 0).val * X =
      X' * CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a 1).val := by
    rw [hX', mul_assoc _ (CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (-(a 1)).val),
      ← CFSG.RankThree.PartTwo.Census.threeCycleMat_pow_val_add,
      show -(a 1) + a 1 = 0 from neg_add_cancel _, ZMod.val_zero, pow_zero, mul_one]
  ext ⟨i, b⟩ ⟨j, b'⟩
  simp only [mul_apply, Fintype.sum_prod_type, sBlockMat, blockDiagonal_apply, yMat, of_apply]
  by_cases h : b = 0 ∧ b' = 1
  · obtain ⟨rfl, rfl⟩ := h
    have := congrFun (congrFun key i) j
    simp only [mul_apply] at this
    simpa [ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
  · have h1 : ∀ k c, (if b = c then
        (CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a b).val) i k else 0) *
        (if c = 0 ∧ b' = 1 then X k j else 0) = 0 := by
      intro k c
      by_cases hbc : b = c
      · subst hbc
        rw [ite_eq_right h, mul_zero]
      · rw [ite_eq_right hbc, zero_mul]
    have h2 : ∀ k c, (if b = 0 ∧ c = 1 then X' i k else 0) *
        (if c = b' then
          (CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a c).val) k j else 0) = 0 := by
      intro k c
      by_cases hc : c = b'
      · subst hc
        rw [ite_eq_right h, zero_mul]
      · rw [ite_eq_right hc, mul_zero]
    simp only [h1, h2, Finset.sum_const_zero]

private theorem eq_one_of_sHom_entry {r : ℕ} {a : Multiplicative (Fin 5 → ZMod 3)}
    (h : ∀ b : Fin 5, ((sHom r K a : SpecialLinearGroup (Idx r) K) :
      Matrix (Idx r) (Idx r) K) (.inl (0, b)) (.inl (1, b)) = 0) : a = 1 := by
  apply Multiplicative.toAdd.injective
  funext b
  have hb := h b
  rw [coe_sHom, fromBlocks_apply₁₁, sBlockMat, blockDiagonal_apply] at hb
  simp only [ite_true] at hb
  exact CFSG.RankThree.PartTwo.Census.threeCycleMat_pow_val_zero_one hb

private theorem sHom_injective (r : ℕ) (K : Type) [Field K] [CharP K 2] :
    Function.Injective (sHom r K) := by
  refine (injective_iff_map_eq_one (sHom r K)).mpr fun a ha =>
    eq_one_of_sHom_entry (K := K) (r := r) fun b => ?_
  rw [ha]
  simp

private theorem card_range_sHom (r : ℕ) : Nat.card (sHom r K).range = 3 ^ 5 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (sHom_injective r K)).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem isElemAbelian_range_sHom (r : ℕ) :
    CFSG.Open.IsElemAbelian 3 (sHom r K).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact mul_comm x y
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      change 3 • (Multiplicative.toAdd x i) = 0
      generalize Multiplicative.toAdd x i = z
      revert z
      decide
    rw [this, map_one]

private theorem isPGroup_range_uHom (r : ℕ) : IsPGroup 2 (uHom r K).range := by
  intro y
  obtain ⟨X, hX⟩ := y.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, pow_two, Subgroup.coe_mul, ← hX, ← map_mul, OneMemClass.coe_one]
  have hXX : X * X = 1 := by
    apply Multiplicative.toAdd.injective
    ext i j
    simp only [toAdd_mul, toAdd_one, Matrix.add_apply, Matrix.zero_apply,
      CharTwo.add_self_eq_zero]
  rw [hXX, map_one]

private theorem uHom_range_ne_bot (r : ℕ) : (uHom r K).range ≠ ⊥ := by
  intro hbot
  have h1 : uHom r K (Multiplicative.ofAdd 1) ∈ (uHom r K).range := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : ((uHom r K (Multiplicative.ofAdd 1) : SpecialLinearGroup (Idx r) K) :
      Matrix (Idx r) (Idx r) K) (.inl (0, 0)) (.inl (0, 1)) = 0 := by
    rw [h1]; rfl
  have h3 : ((uHom r K (Multiplicative.ofAdd 1) : SpecialLinearGroup (Idx r) K) :
      Matrix (Idx r) (Idx r) K) (.inl (0, 0)) (.inl (0, 1)) = 1 := by
    rw [coe_uHom, fromBlocks_apply₁₁]
    simp [yMat]
  rw [h3] at h2
  exact one_ne_zero h2

private theorem sHom_le_normalizer_uHom (r : ℕ) :
    (sHom r K).range ≤
      Subgroup.normalizer ((uHom r K).range : Set (SpecialLinearGroup (Idx r) K)) := by
  refine CFSG.RankThree.PartTwo.Census.le_normalizer_of_conj_mem ?_
  rintro _ ⟨a, rfl⟩ _ ⟨X, rfl⟩
  refine ⟨Multiplicative.ofAdd
    (CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (a.toAdd 0).val * X.toAdd *
      CFSG.RankThree.PartTwo.Census.threeCycleMat K ^ (-(a.toAdd 1)).val), ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  refine Subtype.ext ?_
  change fromBlocks (1 + yMat _) 0 0 1 * fromBlocks (sBlockMat a.toAdd) 0 0 1 =
    fromBlocks (sBlockMat a.toAdd) 0 0 1 * fromBlocks (1 + yMat X.toAdd) 0 0 1
  rw [fromBlocks_multiply, fromBlocks_multiply, mul_add, add_mul, sBlockMat_mul_yMat]
  simp

theorem localPow5_sl (r : ℕ) :
    ∃ U : Subgroup (SpecialLinearGroup (Idx r) K), IsPGroup 2 U ∧ U ≠ ⊥ ∧
      ∃ E : Subgroup (SpecialLinearGroup (Idx r) K),
        E ≤ Subgroup.normalizer (U : Set (SpecialLinearGroup (Idx r) K)) ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 :=
  ⟨(uHom r K).range, isPGroup_range_uHom r, uHom_range_ne_bot r, (sHom r K).range,
    sHom_le_normalizer_uHom r, isElemAbelian_range_sHom r, card_range_sHom r⟩

end LinFive

inductive LocalPow (G : Type) [Group G] (k : ℕ) : Prop
  | mk (U : Subgroup G) (hU2 : IsPGroup 2 U) (hUne : U ≠ ⊥)
      (E : Subgroup G) (hEU : E ≤ Subgroup.normalizer (U : Set G))
      (hEe : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ k) : LocalPow G k

theorem LocalPow.congr {G H : Type} [Group G] [Group H] (e : G ≃* H) {k : ℕ}
    (h : LocalPow G k) : LocalPow H k := by
  obtain ⟨U, hU2, hU1, E, hEN, hEe, hEc⟩ := h
  refine ⟨U.map e.toMonoidHom, hU2.map e.toMonoidHom, ?_, E.map e.toMonoidHom,
    (Subgroup.map_mono hEN).trans (Subgroup.le_normalizer_map e.toMonoidHom),
    IsElemAbelian.map hEe e.toMonoidHom, ?_⟩
  · intro hbot
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).mp hbot)
  · rw [Subgroup.card_map_of_injective e.injective, hEc]

theorem card_idx (r : ℕ) : Fintype.card (LinFive.Idx r) = 10 + r := by
  change Fintype.card ((Fin 2 × Fin 5) ⊕ Fin r) = 10 + r
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin]

theorem localPow5_sl_fin {m : ℕ} (hm : 10 ≤ m) :
    LocalPow (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) 5 := by
  let eIdx : LinFive.Idx (m - 10) ≃ Fin m :=
    (Fintype.equivFinOfCardEq (card_idx (m - 10))).trans (finCongr (by omega))
  obtain ⟨U, hU2, hUne, E, hEU, hEe, hEcard⟩ :=
    LinFive.localPow5_sl (K := ZMod 2) (m - 10)
  exact LocalPow.congr (CFSG.RankThree.PartTwo.Census.slReindex (ZMod 2) eIdx)
    (LocalPow.mk U hU2 hUne E hEU hEe hEcard)

noncomputable def linEquivSL (m : ℕ) :
    Matrix.SpecialLinearGroup (Fin m) (ZMod 2) ≃*
      ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) :=
  (MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL
      ⟨Matrix.SpecialLinearGroup.toGL_injective,
        CFSG.GroupTheory.GLnTwoSplitting.toGL_surjective_zmod_two⟩).trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin m) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin m → ZMod 2)))

theorem localPow5_fin {m : ℕ} (hm : 10 ≤ m) :
    LocalPow ((Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2)) 5 :=
  LocalPow.congr (linEquivSL m) (localPow5_sl_fin hm)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
