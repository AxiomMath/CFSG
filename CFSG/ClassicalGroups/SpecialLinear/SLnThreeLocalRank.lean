module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalBlock

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open
open scoped Kronecker

variable {K : Type} [Field K] {n : ℕ}

private def leviMat (U : Matrix (Fin 3) (Fin 3) K) : Matrix Blk Blk K :=
  (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ U

private theorem leviMat_apply (U : Matrix (Fin 3) (Fin 3) K) (p q : Fin 2) (i j : Fin 3) :
    leviMat U (p, i) (q, j) = if p = q then U i j else 0 := by
  simp [leviMat, Matrix.one_apply]

private theorem leviMat_mul (U V : Matrix (Fin 3) (Fin 3) K) :
    leviMat (U * V) = leviMat U * leviMat V := by
  unfold leviMat
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

private theorem leviMat_one : leviMat (1 : Matrix (Fin 3) (Fin 3) K) = 1 :=
  Matrix.one_kronecker_one

private theorem det_leviMat (U : Matrix (Fin 3) (Fin 3) K) : (leviMat U).det = U.det ^ 2 := by
  unfold leviMat
  rw [Matrix.det_kronecker]
  simp

private theorem leviMat_injective : Function.Injective (leviMat (K := K)) := by
  intro U V h
  ext i j
  have := congrFun (congrFun h (0, i)) (0, j)
  simpa [leviMat_apply] using this

private def leviMonoidHom : Matrix (Fin 3) (Fin 3) K →* Matrix Blk Blk K where
  toFun := leviMat
  map_one' := leviMat_one
  map_mul' := leviMat_mul

private theorem leviMat_mul_blockDiagonal (U : Matrix (Fin 3) (Fin 3) K)
    (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) (h : ∀ i j, U i j ≠ 0 → M i = M j) :
    leviMat U * Matrix.blockDiagonal M = Matrix.blockDiagonal M * leviMat U := by
  ext ⟨p, i⟩ ⟨q, j⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, leviMat_apply, Matrix.blockDiagonal_apply]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  rcases eq_or_ne (U i j) 0 with h0 | h0
  · simp [h0]
  · rw [h i j h0, mul_comm]

private def leviGL (hn : n = 6 ∨ n = 7) : GL (Fin 3) K →* GL (Fin n) K :=
  (embGL hn).comp (Units.map leviMonoidHom)

private theorem coe_leviGL (hn : n = 6 ∨ n = 7) (U : GL (Fin 3) K) :
    ((leviGL hn U : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      embMat hn (leviMat (U : Matrix (Fin 3) (Fin 3) K)) := rfl

private theorem leviGL_injective (hn : n = 6 ∨ n = 7) :
    Function.Injective (leviGL (K := K) hn) :=
  (embGL_injective hn).comp (Units.map_injective leviMat_injective)

private def leviSL (hn : n = 6 ∨ n = 7) :
    Matrix.SpecialLinearGroup (Fin 3) K →* StatedSL n K :=
  ((leviGL hn).comp Matrix.SpecialLinearGroup.toGL).codRestrict (StatedSL n K) fun U => by
    apply CFSG.Open.StatedAPI.mem_statedSL_of_det
    simp [coe_leviGL, det_embMat, det_leviMat]

private theorem coe_leviSL (hn : n = 6 ∨ n = 7) (U : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((leviSL hn U : StatedSL n K) : GL (Fin n) K) =
      leviGL hn (Matrix.SpecialLinearGroup.toGL U) := rfl

private theorem leviSL_injective (hn : n = 6 ∨ n = 7) :
    Function.Injective (leviSL (K := K) hn) := by
  intro U V h
  have h1 := congrArg (fun g : StatedSL n K => (g : GL (Fin n) K)) h
  simp only [coe_leviSL] at h1
  exact Matrix.SpecialLinearGroup.toGL_injective (leviGL_injective hn h1)

private theorem transvection_mulVec_single_ne :
    ((Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : K) :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 1 1 ≠
        Pi.single 1 1 := by
  intro h
  have h1 := congrFun h 0
  simp [Matrix.mulVec, dotProduct, Matrix.SpecialLinearGroup.transvection_coe,
    Fin.sum_univ_two, Pi.single_apply] at h1

private theorem leviMat_mulVec_single (U : Matrix (Fin 3) (Fin 3) K) (p : Fin 2) (b : Fin 3)
    (q : Fin 2) (k : Fin 3) : (leviMat U *ᵥ (Pi.single (p, b) 1 : Blk → K)) (q, k) =
      if p = q then U k b else 0 := by
  simp [Matrix.mulVec, dotProduct, leviMat_apply, Fintype.sum_prod_type, Pi.single_apply,
    eq_comm]

private theorem leviSL_transvection_mulVec_ne (hn : n = 6 ∨ n = 7) {a b : Fin 3} (hab : a ≠ b)
    (p : Fin 2) :
    ((leviSL hn (Matrix.SpecialLinearGroup.transvection hab (1 : K)) : StatedSL n K) :
        GL (Fin n) K).val *ᵥ vecOfBlk hn (Pi.single (p, b) 1) ≠
      vecOfBlk hn (Pi.single (p, b) 1) := by
  rw [coe_leviSL, coe_leviGL, Ne, embMat_mulVec_vecOfBlk]
  intro h
  have h1 := congrFun h (p, a)
  rw [leviMat_mulVec_single] at h1
  simp [Matrix.SpecialLinearGroup.transvection_coe, hab] at h1

private theorem leviSL_transvection_mulVec_eq (hn : n = 6 ∨ n = 7) {a b c : Fin 3}
    (hac : a ≠ c) (hbc : b ≠ c) (p : Fin 2) :
    ((leviSL hn (Matrix.SpecialLinearGroup.transvection hac (1 : K)) : StatedSL n K) :
        GL (Fin n) K).val *ᵥ vecOfBlk hn (Pi.single (p, b) 1) =
      vecOfBlk hn (Pi.single (p, b) 1) := by
  rw [coe_leviSL, coe_leviGL, embMat_mulVec_vecOfBlk]
  funext ⟨q, k⟩
  rw [leviMat_mulVec_single]
  by_cases hpq : p = q
  · subst hpq
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
      Pi.single_apply, hbc, hbc.symm]
  · simp [hpq, Pi.single_apply]

private theorem transvection_pow {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (k : ℕ) :
    Matrix.SpecialLinearGroup.transvection hij (1 : K) ^ k =
      Matrix.SpecialLinearGroup.transvection hij (k : K) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_succ, Matrix.SpecialLinearGroup.transvection_add hij]

private theorem orderOf_transvection {r : ℕ} [Fact r.Prime] [CharP K r] {ι : Type} [Fintype ι]
    [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    orderOf (Matrix.SpecialLinearGroup.transvection hij (1 : K)) = r := by
  apply orderOf_eq_prime
  · rw [transvection_pow, CharP.cast_eq_zero, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  · intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup ι K => (g : Matrix ι ι K) i j) h
    simp [Matrix.SpecialLinearGroup.transvection_coe, hij] at this

private theorem commute_blockEmb_c₀_of_zero (hn : n = 6 ∨ n = 7) (j : Fin 3)
    (T : Matrix.SpecialLinearGroup (Fin 2) K) (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : Multiplicative.toAdd v j = 0) : Commute (blockEmb hn j T) (c₀ K hn v) :=
  commute_blockEmb_c₀ hn j T v (by rw [hv, blockPowGL_zero]; exact Commute.one_right _)

private theorem commute_leviSL_c₀ (hn : n = 6 ∨ n = 7) (U : Matrix.SpecialLinearGroup (Fin 3) K)
    (v : Multiplicative (Fin 3 → ZMod 3))
    (h : ∀ i j, (U : Matrix (Fin 3) (Fin 3) K) i j ≠ 0 →
      Multiplicative.toAdd v i = Multiplicative.toAdd v j) :
    Commute (leviSL hn U) (c₀ K hn v) := by
  apply Subtype.ext
  show leviGL hn _ * blkGL hn _ = blkGL hn _ * leviGL hn _
  apply Units.ext
  simp only [Units.val_mul, coe_leviGL, coe_blkGL, ← embMat_mul]
  congr 1
  exact leviMat_mul_blockDiagonal _ _ (fun i j hij => by simp [h i j hij])

private theorem commute_leviSL_blockEmb (hn : n = 6 ∨ n = 7)
    (U : Matrix.SpecialLinearGroup (Fin 3) K) (j : Fin 3)
    (T : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : ∀ i k, (U : Matrix (Fin 3) (Fin 3) K) i k ≠ 0 → i = k ∨ (i ≠ j ∧ k ≠ j)) :
    Commute (leviSL hn U) (blockEmb hn j T) := by
  apply Subtype.ext
  show leviGL hn _ * blkGL hn _ = blkGL hn _ * leviGL hn _
  apply Units.ext
  simp only [Units.val_mul, coe_leviGL, coe_blkGL, ← embMat_mul]
  congr 1
  refine leviMat_mul_blockDiagonal _ _ (fun i k hik => ?_)
  rcases h i k hik with rfl | ⟨hi, hk⟩
  · rfl
  · simp [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hk]

private theorem commute_transvection_zero {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    Commute (Matrix.SpecialLinearGroup.transvection hab (1 : K))
      (Matrix.SpecialLinearGroup.transvection hac (1 : K)) := by
  apply Subtype.ext
  show _ * _ = _ * _
  simp [Matrix.SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    Matrix.single_mul_single_of_ne, hab.symm, hac.symm]
  abel

private theorem transvection_entry_ne_zero {a b : Fin 3} (hab : a ≠ b) {i j : Fin 3}
    (h : (Matrix.SpecialLinearGroup.transvection hab (1 : K) : Matrix (Fin 3) (Fin 3) K) i j ≠
      0) : i = j ∨ (i = a ∧ j = b) := by
  by_cases h1 : i = j
  · exact Or.inl h1
  by_cases h2 : i = a ∧ j = b
  · exact Or.inr h2
  exfalso
  apply h
  have h3 : ¬ (a = i ∧ b = j) := fun ⟨e1, e2⟩ => h2 ⟨e1.symm, e2.symm⟩
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply, h1, h3]

variable [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]

private theorem orderOf_blockEmb_transvection (hn : n = 6 ∨ n = 7) (j : Fin 3) :
    orderOf (blockEmb hn j (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (1 : K))) = r := by
  rw [orderOf_blockEmb, orderOf_transvection]

private theorem orderOf_leviSL_transvection (hn : n = 6 ∨ n = 7) {a b : Fin 3} (hab : a ≠ b) :
    orderOf (leviSL hn (Matrix.SpecialLinearGroup.transvection hab (1 : K))) = r := by
  have h := orderOf_injective (leviSL (K := K) hn) (leviSL_injective hn)
    (Matrix.SpecialLinearGroup.transvection hab (1 : K))
  rw [h]
  exact orderOf_transvection (r := r) _

theorem two_le_pRank_centralizer_c₀_weight_one (hn : n = 6 ∨ n = 7) :
    2 ≤ pRank r (Subgroup.centralizer
      ({c₀ K hn (Multiplicative.ofAdd ![1, 0, 0])} : Set (StatedSL n K))) := by
  refine two_le_pRank_of_mulVec (r := r) (x := blockEmb hn 1 _) (y := blockEmb hn 2 _)
    (w := vecOfBlk hn (Pi.single (1, 2) 1)) ?_ ?_ (orderOf_blockEmb_transvection hn 1)
    (orderOf_blockEmb_transvection hn 2) (commute_blockEmb_blockEmb hn (by decide) _ _)
    (blockEmb_mulVec_vecOfBlk_of_ne hn (by decide) _ 1)
    (blockEmb_mulVec_vecOfBlk_ne_of hn 2 _ 1 transvection_mulVec_single_ne)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_blockEmb_c₀_of_zero hn 1 _ _ (by simp)).eq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_blockEmb_c₀_of_zero hn 2 _ _ (by simp)).eq

theorem two_le_pRank_centralizer_c₀_weight_two (hn : n = 6 ∨ n = 7) :
    2 ≤ pRank r (Subgroup.centralizer
      ({c₀ K hn (Multiplicative.ofAdd ![1, 1, 0])} : Set (StatedSL n K))) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  refine two_le_pRank_of_mulVec (r := r) (x := blockEmb hn 2 _)
    (y := leviSL hn (Matrix.SpecialLinearGroup.transvection h01 (1 : K)))
    (w := vecOfBlk hn (Pi.single (0, 1) 1)) ?_ ?_ (orderOf_blockEmb_transvection hn 2)
    (orderOf_leviSL_transvection hn h01) ?_
    (blockEmb_mulVec_vecOfBlk_of_ne hn (by decide) _ 0)
    (leviSL_transvection_mulVec_ne hn h01 0)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_blockEmb_c₀_of_zero hn 2 _ _ (by simp)).eq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    refine (commute_leviSL_c₀ hn _ _ fun i j hij => ?_).eq
    rcases transvection_entry_ne_zero h01 hij with rfl | ⟨rfl, rfl⟩
    · rfl
    · rfl
  · refine (commute_leviSL_blockEmb hn _ 2 _ fun i k hik => ?_).symm
    rcases transvection_entry_ne_zero h01 hik with h | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨by decide, by decide⟩

theorem two_le_pRank_centralizer_c₀_weight_three (hn : n = 6 ∨ n = 7) :
    2 ≤ pRank r (Subgroup.centralizer
      ({c₀ K hn (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSL n K))) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have hc : ∀ {a b : Fin 3} (hab : a ≠ b), (leviSL hn (Matrix.SpecialLinearGroup.transvection
      hab (1 : K)) : StatedSL n K) ∈ Subgroup.centralizer
        ({c₀ K hn (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSL n K)) := by
    intro a b hab
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine (commute_leviSL_c₀ hn _ _ fun i j _ => ?_).eq
    fin_cases i <;> fin_cases j <;> rfl
  refine two_le_pRank_of_mulVec (r := r)
    (x := leviSL hn (Matrix.SpecialLinearGroup.transvection h01 (1 : K)))
    (y := leviSL hn (Matrix.SpecialLinearGroup.transvection h02 (1 : K)))
    (w := vecOfBlk hn (Pi.single (0, 2) 1)) (hc h01) (hc h02) (orderOf_leviSL_transvection hn h01)
    (orderOf_leviSL_transvection hn h02)
    (Commute.map (commute_transvection_zero h01 h02 (by decide)) (leviSL hn))
    (leviSL_transvection_mulVec_eq hn h01 (by decide) 0) (leviSL_transvection_mulVec_ne hn h02 0)

theorem one_le_pRank_centralizer_c₀_plane_a (hn : n = 6 ∨ n = 7) :
    1 ≤ pRank r (Subgroup.centralizer
      ({c₀ K hn (Multiplicative.ofAdd ![1, 0, 0]), c₀ K hn (Multiplicative.ofAdd ![0, 1, 0])} :
        Set (StatedSL n K))) := by
  refine one_le_pRank_of_orderOf (x := blockEmb hn 2 (Matrix.SpecialLinearGroup.transvection
    (show (0 : Fin 2) ≠ 1 by decide) (1 : K))) ?_ (orderOf_blockEmb_transvection hn 2)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | hh
  · exact (commute_blockEmb_c₀_of_zero hn 2 _ _ (by simp)).symm.eq
  · rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commute_blockEmb_c₀_of_zero hn 2 _ _ (by simp)).symm.eq

theorem one_le_pRank_centralizer_c₀_plane_b (hn : n = 6 ∨ n = 7) :
    1 ≤ pRank r (Subgroup.centralizer
      ({c₀ K hn (Multiplicative.ofAdd ![1, 1, 1]), c₀ K hn (Multiplicative.ofAdd ![0, 0, 1])} :
        Set (StatedSL n K))) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  refine one_le_pRank_of_orderOf
    (x := leviSL hn (Matrix.SpecialLinearGroup.transvection h01 (1 : K))) ?_
    (orderOf_leviSL_transvection hn h01)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | hh
  · refine (commute_leviSL_c₀ hn _ _ fun i j _ => ?_).symm.eq
    fin_cases i <;> fin_cases j <;> rfl
  · rw [Set.mem_singleton_iff] at hh
    subst hh
    refine (commute_leviSL_c₀ hn _ _ fun i j hij => ?_).symm.eq
    rcases transvection_entry_ne_zero h01 hij with rfl | ⟨rfl, rfl⟩
    · rfl
    · rfl

end CFSG.ClassicalGroups.SLnThreeLocal
