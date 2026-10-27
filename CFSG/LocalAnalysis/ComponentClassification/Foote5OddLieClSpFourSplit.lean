module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpFourLeg
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpThree

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

abbrev qMat (K : Type) [Field K] : Fin 2 → Matrix (Fin 2) (Fin 2) K :=
  ![!![1, 1; 1, -1], !![1, -1; -1, -1]]

theorem zmod_three_pow_eight_of_commute_qMat : ∀ (k : Fin 2) (a b c d : ZMod 3),
    !![a, b; c, d] * qMat (ZMod 3) k = qMat (ZMod 3) k * !![a, b; c, d] →
    a * d - b * c ≠ 0 → !![a, b; c, d] ^ 8 = 1 := by
  decide

theorem pow_eight_of_commute_qMat [Finite K] (h3 : Nat.card K = 3) (k : Fin 2)
    {P : Matrix (Fin 2) (Fin 2) K} (hP : P * qMat K k = qMat K k * P) (hdet : P.det ≠ 0) :
    P ^ 8 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 3) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  set f : K →+* ZMod 3 := (FiniteField.ringEquivOfCardEq hc).toRingHom
  have hfinj : Function.Injective f := (FiniteField.ringEquivOfCardEq hc).injective
  have hinj : ∀ M N : Matrix (Fin 2) (Fin 2) K, M.map f = N.map f → M = N := fun M N h => by
    ext i j
    exact hfinj (congrFun (congrFun h i) j)
  have hg : (qMat K k).map f = qMat (ZMod 3) k := by
    ext i j
    fin_cases k <;> fin_cases i <;> fin_cases j <;> simp
  have hP' := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M.map f) hP
  simp only [Matrix.map_mul, hg] at hP'
  have hdet' : (P.map f).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero f).2 hdet
  apply hinj
  rw [Matrix.map_pow, Matrix.map_one f (map_zero f) (map_one f)]
  have hXe := eta_fin_two (P.map f)
  rw [hXe] at hP' hdet' ⊢
  rw [det_fin_two_of] at hdet'
  exact zmod_three_pow_eight_of_commute_qMat k _ _ _ _ hP' hdet'

theorem conjAut_pow_eight_of_commute_qMat [Finite K] (h3 : Nat.card K = 3) (k : Fin 2)
    {D : gsp 2 K}
    (hDA : ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      stdSkew 2 K = stdSkew 2 K * ((D : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (hDS : ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      fromBlocks (qMat K k) 0 0 (-qMat K k) = fromBlocks (qMat K k) 0 0 (-qMat K k) *
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    conjAut 2 K (D ^ 2 ^ 3) = 1 := by
  have h2 := two_ne_zero_of_three h3
  set M := ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hblk := fromBlocks_of_commute_stdSkew h2 hDA
  have hdet : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).1 (D : GL (Fin 2 ⊕ Fin 2) K).isUnit).ne_zero
  rw [hblk, det_fromBlocks_zero₂₁] at hdet
  rw [hblk, fromBlocks_multiply, fromBlocks_multiply] at hDS
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hDS
  obtain ⟨h11, -, -, h22⟩ := Matrix.fromBlocks_inj.1 hDS
  have h22' : M.toBlocks₂₂ * qMat K k = qMat K k * M.toBlocks₂₂ := by
    rw [Matrix.mul_neg, Matrix.neg_mul] at h22
    exact neg_inj.1 h22
  have hP8 := pow_eight_of_commute_qMat h3 k h11 (left_ne_zero_of_mul hdet)
  have hR8 := pow_eight_of_commute_qMat h3 k h22' (right_ne_zero_of_mul hdet)
  rw [conjAut_eq_one_iff (by norm_num)]
  refine ⟨1, Units.ext ?_⟩
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hM, hblk, show 2 ^ 3 = 8 by norm_num,
    fromBlocks_diag_pow, hP8, hR8, fromBlocks_one, map_one, Units.val_one]

theorem qMat_mul_self (h3K : (3 : K) = 0) (k : Fin 2) : qMat K k * qMat K k = (-1 : K) • 1 := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h3K

theorem qMat_transpose (k : Fin 2) : (qMat K k)ᵀ = qMat K k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem fourMat_two_mul_qMat : fourMat K 2 * qMat K 0 = qMat K 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_leviSL_qMat (h3K : (3 : K) = 0) (k : Fin 2) {q : SL(2, K)}
    (hq : (q : Matrix (Fin 2) (Fin 2) K) = qMat K k) :
    (((leviSL 2 K q : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (qMat K k) 0 0 (-qMat K k) := by
  have hinv : ((q⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -qMat K k := by
    have e : q * ⟨-qMat K k, by
        rw [← hq, Matrix.det_neg, Fintype.card_fin, q.2]; norm_num⟩ = 1 := by
      apply Subtype.ext
      change (q : Matrix (Fin 2) (Fin 2) K) * -qMat K k = 1
      rw [hq, Matrix.mul_neg, qMat_mul_self h3K, neg_smul, one_smul, neg_neg]
    rw [inv_eq_of_mul_eq_one_right e]
  rw [coe_leviSL, hq, hinv, transpose_neg, qMat_transpose]

theorem coe_leviSL_fourMat_two {q : SL(2, K)}
    (hq : (q : Matrix (Fin 2) (Fin 2) K) = fourMat K 2) :
    (((leviSL 2 K q : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (fourMat K 2) 0 0 (fourMat K 2) := by
  have hinv : ((q⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = (fourMat K 2)ᵀ := by
    have e : q * ⟨(fourMat K 2)ᵀ, by rw [det_transpose, ← hq, q.2]⟩ = 1 := by
      apply Subtype.ext
      change (q : Matrix (Fin 2) (Fin 2) K) * (fourMat K 2)ᵀ = 1
      rw [hq]
      exact mul_eq_one_comm.1 (fourMat_orth 2)
    rw [inv_eq_of_mul_eq_one_right e]
  rw [coe_leviSL, hq, hinv, transpose_transpose]

theorem eq_one_skewSplit_three [Finite K] (h3 : Nat.card K = 3)
    {R : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut 2 K (stdSkewGsp 2 K) = conjAut 2 K (stdSkewGsp 2 K) * y)
    (hRc : ∀ s, conjAut 2 K (stdSkewGsp 2 K) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ y ∈ R, y = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h2 := two_ne_zero_of_three h3
  have hK : ringChar K ≠ 2 := fun h => h2 (by
    have := ringChar.spec K 2
    exact_mod_cast (this.2 (by rw [h])))
  have h3K : (3 : K) = 0 := by
    have := FiniteField.cast_card_eq_zero K
    rwa [← Nat.card_eq_fintype_card, h3, Nat.cast_ofNat] at this
  set θ := (proj 2 K).comp (leviSL 2 K) with hθ
  have hθfix : ∀ e, conjAut 2 K (stdSkewGsp 2 K) (θ e) = θ e := fun e => by
    rw [hθ, MonoidHom.comp_apply, conjAut_proj]
    exact congrArg (proj 2 K) (leviSL_mem_spCent e)
  have hnorm : ∀ X : SL(2, K), ∀ y ∈ R, conjProjH (StatedSp 2 K) (leviSL 2 K X) * y *
      (conjProjH (StatedSp 2 K) (leviSL 2 K X))⁻¹ ∈ R :=
    fun X y hy => conj_mem_of_mem_closure hRc (mem_closure_fix hK θ hθfix X) hy
  have hdet₁ : (fourMat K 2).det = 1 := by simp [Matrix.det_fin_two]
  have hdet₂ : (qMat K 0).det = 1 := by
    simp [Matrix.det_fin_two]
    linear_combination -h3K
  set q₁ : SL(2, K) := ⟨fourMat K 2, hdet₁⟩ with hq₁
  set q₂ : SL(2, K) := ⟨qMat K 0, hdet₂⟩ with hq₂
  have hL₁ := coe_leviSL_fourMat_two (q := q₁) rfl
  have hL₂ := coe_leviSL_qMat h3K 0 (q := q₂) rfl
  have hL₃ := coe_leviSL_qMat h3K 1 (q := q₁ * q₂) (by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact fourMat_two_mul_qMat)
  have hsqm : ∀ (S : StatedSp 2 K) (X Y : Matrix (Fin 2) (Fin 2) K),
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks X 0 0 Y → X * X = (-1 : K) • 1 → Y * Y = (-1 : K) • 1 →
      conjProjH (StatedSp 2 K) S * conjProjH (StatedSp 2 K) S = 1 := by
    intro S X Y hS hX hY
    rw [← map_mul]
    refine conjProjH_eq_one_of_smul (by norm_num) (neg_ne_zero.2 one_ne_zero) ?_
    rw [Subgroup.coe_mul, Units.val_mul, hS, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hX, hY]
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero]
  have hf2 : fourMat K 2 * fourMat K 2 = (-1 : K) • 1 := by
    rw [fourMat_sq]
    simp
  have hq2 : ∀ k : Fin 2, -qMat K k * -qMat K k = (-1 : K) • 1 := fun k => by
    rw [neg_mul_neg, qMat_mul_self h3K]
  have hAA : ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((stdSkewGsp 2 K : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (1 : K) • 1 := by
    rw [coe_stdSkewGsp, stdSkew_mul_self, one_smul]
  have hsqS : ∀ (S : StatedSp 2 K) (X Y : Matrix (Fin 2) (Fin 2) K),
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks X 0 0 Y → X * X = (-1 : K) • 1 → Y * Y = (-1 : K) • 1 →
      ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (-1 : K) • 1 := by
    intro S X Y hS hX hY
    rw [hS, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hX, hY]
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero]
  have hfpf₁ : ∀ x ∈ R, conjProjH (StatedSp 2 K) (leviSL 2 K q₁) * x =
      x * conjProjH (StatedSp 2 K) (leviSL 2 K q₁) → x = 1 := fun x hx hc =>
    eq_one_of_commute_leg_of_odd h3 le_rfl one_ne_zero hAA (neg_ne_zero.2 one_ne_zero)
      (hsqS _ _ _ hL₁ hf2 hf2) (fun D hDA hDS => ⟨3, conjAut_pow_eight_of_commute_fourMat h3 2
        (by rwa [coe_stdSkewGsp] at hDA) (by rwa [hL₁] at hDS)⟩)
      (odd_orderOf_of_mem hRodd hx) (hRi x hx) hc.symm
  have hfpf : ∀ (k : Fin 2) (q : SL(2, K)),
      ((leviSL 2 K q : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        fromBlocks (qMat K k) 0 0 (-qMat K k) →
      ∀ x ∈ R, conjProjH (StatedSp 2 K) (leviSL 2 K q) * x =
        x * conjProjH (StatedSp 2 K) (leviSL 2 K q) → x = 1 := fun k q hL x hx hc =>
    eq_one_of_commute_leg_of_odd h3 le_rfl one_ne_zero hAA (neg_ne_zero.2 one_ne_zero)
      (hsqS _ _ _ hL (qMat_mul_self h3K k) (hq2 k)) (fun D hDA hDS =>
        ⟨3, conjAut_pow_eight_of_commute_qMat h3 k (by rwa [coe_stdSkewGsp] at hDA)
          (by rwa [hL] at hDS)⟩)
      (odd_orderOf_of_mem hRodd hx) (hRi x hx) hc.symm
  have hRb : R = ⊥ := eq_bot_of_four_group (s₁ := conjProjH (StatedSp 2 K) (leviSL 2 K q₁))
    (s₂ := conjProjH (StatedSp 2 K) (leviSL 2 K q₂)) (hsqm _ _ _ hL₁ hf2 hf2)
    (hsqm _ _ _ hL₂ (qMat_mul_self h3K 0) (hq2 0)) (fun x hx => hnorm q₁ x hx)
    (fun x hx => hnorm q₂ x hx) hfpf₁ (hfpf 0 q₂ hL₂) (by
      rw [← map_mul, ← map_mul]
      exact hfpf 1 _ hL₃)
  intro y hy
  rw [hRb] at hy
  exact mem_bot.1 hy

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
