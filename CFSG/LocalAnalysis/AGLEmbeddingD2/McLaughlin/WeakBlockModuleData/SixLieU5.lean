module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUOddK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PSURank3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.LieType.CurtisTits

variable {F : Type} [Field F] [Finite F] [CharP F 2]

section Mats

variable {ω : F}

@[expose] def eltA (ω : F) : Matrix (Fin 3) (Fin 3) F := !![ω, 0, 0; 0, ω, 0; 0, 0, ω]

@[expose] def eltAInv (ω : F) : Matrix (Fin 3) (Fin 3) F :=
  !![ω ^ 2, 0, 0; 0, ω ^ 2, 0; 0, 0, ω ^ 2]

@[expose] def eltB : Matrix (Fin 3) (Fin 3) F := !![1, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] def eltBInv : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 1]

theorem eltA_eq_scalar : eltA ω = Matrix.scalar (Fin 3) ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eltA]

omit [Finite F] in
theorem eltA_mul_inv (hω3 : ω ^ 3 = 1) :
    eltA ω * eltAInv ω = 1 ∧ eltAInv ω * eltA ω = 1 := by
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [eltA, eltAInv, mul_apply, Fin.sum_univ_three] <;>
      linear_combination hω3

omit [Finite F] in
theorem eltB_mul_inv :
    (eltB : Matrix (Fin 3) (Fin 3) F) * (eltBInv : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      (eltBInv : Matrix (Fin 3) (Fin 3) F) * (eltB : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  refine ⟨?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [eltB, eltBInv, mul_apply, Fin.sum_univ_three, h2]

theorem eltA_mem_SU (hω3 : ω ^ 3 = 1) (hσ : unitaryInvolution F 2 1 ω = ω ^ 2) :
    (⟨eltA ω, eltAInv ω, (eltA_mul_inv hω3).1, (eltA_mul_inv hω3).2⟩ : GL (Fin 3) F) ∈
      SU (unitaryInvolution F 2 1) 3 := by
  rw [mem_SU]
  refine ⟨by simp [eltA, det_fin_three]; linear_combination hω3, ?_⟩
  change conjTr (unitaryInvolution F 2 1) (eltA ω) * antidiag 3 * eltA ω = antidiag 3
  rw [eltA, CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.conjTr_fin_three,
    antidiag_three_eq_matrix]
  simp only [map_zero, hσ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> linear_combination (hω3)

theorem eltB_mem_SU :
    (⟨eltB, eltBInv, eltB_mul_inv.1, eltB_mul_inv.2⟩ : GL (Fin 3) F) ∈
      SU (unitaryInvolution F 2 1) 3 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [mem_SU]
  refine ⟨by simp [eltB, det_fin_three]; rw [neg_eq_iff_add_eq_zero]; exact h2, ?_⟩
  change conjTr (unitaryInvolution F 2 1) (eltB : Matrix (Fin 3) (Fin 3) F) * antidiag 3 * eltB =
    antidiag 3
  rw [eltB, CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.conjTr_fin_three,
    antidiag_three_eq_matrix]
  simp only [map_one, map_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h2]

end Mats


section Lift

theorem commute_diag_of_block {σ : F ≃+* F} {n r : ℕ} {e : Fin r → Fin n} {t : Fin n → F}
    {d q : SU σ n} (hd : mat σ n d = diagonal t) (hq : IsBlkOn e (mat σ n q))
    (hc : ∀ i j, t (e i) * mat σ n q (e i) (e j) = mat σ n q (e i) (e j) * t (e j)) :
    d * q = q * d := by
  classical
  apply mat_injective
  rw [map_mul, map_mul, hd]
  ext a b
  rw [diagonal_mul, mul_diagonal]
  by_cases hab : a ∈ Set.range e ∧ b ∈ Set.range e
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hab
    exact hc i j
  · have h1 := hq a b (by tauto)
    rw [h1]
    by_cases h : a = b
    · subst h; simp
    · simp [one_apply_ne h]

variable (hF : Nat.card F = (2 ^ 1) ^ 2) {n : ℕ}

include hF in
theorem exists_su_odd_triple (hn5 : 5 ≤ n) (hn : ¬Even n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) :
    ∃ x y z : SU (unitaryInvolution F 2 1) n,
      x ∈ rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n) k ∧
      y ∈ rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n) k ∧
      z ∈ (⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i) ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ z ^ 3 = 1 ∧ x * y = y * x ∧ x * z = z * x ∧ y * z = z * y ∧
      x ≠ 1 ∧ (∀ m : ℕ, x ^ m ≠ y) ∧ ∀ a b : ℕ, x ^ a * y ^ b ≠ z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ω, hω0, hω1, hω3⟩ := exists_primitive_cube_root_of_card_four hF
  have hσω : unitaryInvolution F 2 1 ω = ω ^ 2 := by rw [unitaryInvolution_apply, pow_one]
  have hωinv : ω⁻¹ = ω ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', hω3]
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hn
  have hkv : k.val + 1 = n / 2 := by have := k.isLt; omega
  set k' : Fin (n / 2) := ⟨k.val - 1, by omega⟩ with hk'
  have h' : k'.val + 1 < n / 2 := by simp only [hk']; omega
  set d := shortTorus (unitaryInvolution F 2 1) hσ (lowIdx_ne_succ h') (lowIdx_ne_rev k' k')
    (lowIdx_ne_rev _ _) ((Units.mk0 ω hω0 : Fˣ) : F) with hd
  have hdT' : d ∈ levelTorus (unitaryInvolution F 2 1) k' :=
    shortTorus_mem_levelTorus hσ h' _
  have hdT : d ∈ ⨆ i, levelTorus (unitaryInvolution F 2 1) (n := n) i :=
    Subgroup.mem_iSup_of_mem k' hdT'
  set t := shortTorusFun (unitaryInvolution F 2 1) (lowIdx k') (lowIdx ⟨k'.val + 1, h'⟩) ω
    with ht
  have hdmat : mat (unitaryInvolution F 2 1) n d = diagonal t :=
    coe_shortTorus _ hσ _ _ _ (lowIdx_ne_rev _ _) hω0
  set e := lastIdxOdd k hn with he
  have hD : diagonal (t ∘ e) = !![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] := by
    have ht0 : t (lowIdx k) = ω ^ 2 := by
      simp only [ht, shortTorusFun]
      rw [ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, hk']; omega),
        ite_eq_left (by simp [Fin.ext_iff, val_lowIdx, hk']; omega), hωinv]
    have ht1 : t (midIdx n hn) = 1 := by
      simp only [ht, shortTorusFun]
      rw [ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, Fin.val_rev, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, midIdx, Fin.val_rev, hk']; omega)]
    have ht2 : t (Fin.rev (lowIdx k)) = ω ^ 2 := by
      simp only [ht, shortTorusFun]
      rw [ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega),
        ite_eq_right (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega),
        ite_eq_left (by simp [Fin.ext_iff, val_lowIdx, Fin.val_rev, hk']; omega), hσω]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [he, lastIdxOdd, ht0, ht1, ht2]
  have htD : ∀ i, t (e i) = (!![ω ^ 2, 0, 0; 0, 1, 0; 0, 0, ω ^ 2] : Matrix (Fin 3) (Fin 3) F) i i :=
    fun i => by
      have := congrFun (congrFun hD i) i
      simpa using this
  set eL := rankOneLastOddEquiv hF hn hk with heL
  have hblock : ∀ g : rankOne (rootGroup (unitaryInvolution F 2 1) hσ n) k,
      mat (unitaryInvolution F 2 1) 3 (eL g) = (mat (unitaryInvolution F 2 1) n g).submatrix e e :=
    fun g => by rw [heL, mat_rankOneLastOddEquiv, toBlock3_eq_submatrix]; rfl
  have hω3' : ω ^ 3 = 1 := hω3
  let A3 : SU (unitaryInvolution F 2 1) 3 := ⟨_, eltA_mem_SU hω3' hσω⟩
  let B3 : SU (unitaryInvolution F 2 1) 3 := ⟨_, eltB_mem_SU⟩
  have hA3 : mat (unitaryInvolution F 2 1) 3 A3 = eltA ω := rfl
  have hB3 : mat (unitaryInvolution F 2 1) 3 B3 = eltB := rfl
  set X := eL.symm A3 with hX
  set Y := eL.symm B3 with hY
  have hXm : (mat (unitaryInvolution F 2 1) n (X : SU _ n)).submatrix e e = eltA ω := by
    rw [← hblock, hX, MulEquiv.apply_symm_apply, hA3]
  have hYm : (mat (unitaryInvolution F 2 1) n (Y : SU _ n)).submatrix e e = eltB := by
    rw [← hblock, hY, MulEquiv.apply_symm_apply, hB3]
  have hF3 : Nat.card F - 1 = 3 := by rw [hF]; norm_num
  have hz3 : d ^ 3 = 1 := by
    have := diag_pow_eq_one (levelTorus_le_diagSubgroup k' hdT')
    rwa [hF3] at this
  have hcommX : (d : SU _ n) * (X : SU _ n) = (X : SU _ n) * d := by
    refine commute_diag_of_block hdmat (isBlkOn_lastIdxOdd hn hk X.2) fun i j => ?_
    have h1 := congrFun (congrFun hXm i) j
    simp only [submatrix_apply] at h1
    rw [h1, htD i, htD j]
    fin_cases i <;> fin_cases j <;> simp [eltA] <;> ring
  have hcommY : (d : SU _ n) * (Y : SU _ n) = (Y : SU _ n) * d := by
    refine commute_diag_of_block hdmat (isBlkOn_lastIdxOdd hn hk Y.2) fun i j => ?_
    have h1 := congrFun (congrFun hYm i) j
    simp only [submatrix_apply] at h1
    rw [h1, htD i, htD j]
    fin_cases i <;> fin_cases j <;> simp [eltB] <;> ring
  have hAB : A3 * B3 = B3 * A3 := by
    apply mat_injective
    rw [map_mul, map_mul, hA3, hB3, eltA_eq_scalar]
    exact (Matrix.scalar_commute ω (fun r => mul_comm _ r) _).eq
  have hA33 : A3 ^ 3 = 1 := by
    apply mat_injective
    rw [map_pow, hA3, eltA_eq_scalar, ← map_pow, hω3', map_one, map_one]
  have hB33 : B3 ^ 3 = 1 := by
    apply mat_injective
    have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [map_pow, hB3, map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [eltB, pow_succ, mul_apply, Fin.sum_univ_three, h2]
  have hX3 : X ^ 3 = 1 := by
    apply eL.injective
    rw [hX, map_pow, MulEquiv.apply_symm_apply, hA33, map_one]
  have hY3 : Y ^ 3 = 1 := by
    apply eL.injective
    rw [hY, map_pow, MulEquiv.apply_symm_apply, hB33, map_one]
  have hXY : X * Y = Y * X := by
    apply eL.injective
    rw [map_mul, map_mul, hX, hY, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hAB]
  refine ⟨X, Y, d, X.2, Y.2, hdT, by simpa using congrArg Subtype.val hX3,
    by simpa using congrArg Subtype.val hY3, hz3, by simpa using congrArg Subtype.val hXY,
    hcommX.symm, hcommY.symm, ?_, ?_, ?_⟩
  · intro h1
    have h1' : X = 1 := Subtype.ext h1
    have := congrArg (fun g => (mat (unitaryInvolution F 2 1) 3 (eL g)) 0 0) h1'
    simp only [hX, MulEquiv.apply_symm_apply, hA3, map_one, eltA] at this
    simp at this
    exact hω1 this
  · intro m hm
    have hm' : X ^ m = Y := Subtype.ext (by simpa using hm)
    have := congrArg (fun g => (mat (unitaryInvolution F 2 1) 3 (eL g)) 0 2) hm'
    simp only [map_pow, hX, hY, MulEquiv.apply_symm_apply] at this
    rw [hA3, hB3, eltA_eq_scalar, ← map_pow] at this
    simp [eltB] at this
  · intro a b hab
    have hmem : d ∈ rankOne (rootGroup (unitaryInvolution F 2 1) hσ n) k := by
      rw [← hab]
      exact mul_mem (pow_mem X.2 a) (pow_mem Y.2 b)
    have hblk := isBlkOn_lastIdxOdd hn hk hmem
    set p : Fin n := lowIdx k' with hp
    have hp' : p ∉ Set.range e := by
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      fin_cases i <;> simp [he, lastIdxOdd, hp, val_lowIdx, midIdx, Fin.val_rev, hk'] at this <;>
        omega
    have h1 := hblk p p (Or.inl hp')
    rw [hdmat, diagonal_apply_eq, one_apply_eq, ht] at h1
    simp [shortTorusFun] at h1
    exact hω1 h1

include hF in
theorem three_le_pRank_of_su_odd_node (hn5 : 5 ≤ n) (hn : ¬Even n) {k : Fin (n / 2)}
    (hk : ¬k.val + 1 < n / 2) {Y : Type} [Group Y] [Finite Y]
    (π' : SU (unitaryInvolution F 2 1) n →* Y) (hinj : Function.Injective π') (J : Subgroup Y)
    (hBJ : ∀ b ∈ borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 1)), π' b ∈ J)
    (hLJ : rankOne (rootGroup (unitaryInvolution F 2 1) (unitaryInvolution_involutive hF) n) k ≤
      J.comap π') :
    3 ≤ CFSG.Open.pRank 3 J := by
  obtain ⟨x, y, z, hx, hy, hz, hx3, hy3, hz3, hxy, hxz, hyz, hx1, hxn, hxyn⟩ :=
    exists_su_odd_triple hF hn5 hn hk
  exact three_le_pRank_of_lifted π' (fun w hw _ => by
      have := hinj (show π' w = π' 1 by rw [map_one]; exact hw)
      exact this) J x y z (hLJ hx) (hLJ hy) (hBJ z (iSup_le_borel hz)) hx3 hy3 hz3 hxy hxz hyz
    hx1 hxn hxyn

end Lift

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
