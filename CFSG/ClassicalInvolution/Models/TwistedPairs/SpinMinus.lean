module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.Basic
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinMap
public import CFSG.ClassicalInvolution.WeakCT.SpTorus
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne
public import CFSG.LieType.Steinberg.Classical.SpinOdd.RankOne
public import CFSG.LieType.Universal.Spin.Twisted.Torus
public import CFSG.CharacterTheory.Semidihedral.DefiningCharacteristicDimension
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree

public section

namespace CFSG.ClassicalInvolution.Models.TwistedPairs

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.Timmesfeld.RankTwo
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F] {b c : F}

theorem fin_zero_ne_one : (⟨0, by decide⟩ : Fin (3 - 1)) ≠ ⟨1, by decide⟩ := by decide

@[expose] noncomputable def minusLongBlock (b c : F) :
    SL(2, F) →* spinGroup (quadMinus 3 F b c) :=
  (minusFrame 3 b c).longSL2 fin_zero_ne_one true false

section Short

variable [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def shortBlock (n : ℕ) (k : Fin (n - 1)) :
    SL(2, ShortField b c) →* spinGroup (quadMinus n F b c) :=
  haveI := finite_shortField (b := b) (c := c)
  Classical.choose (exists_hom_of_rankOneRels (shortRels n hirr k))

theorem shortBlock_upper (n : ℕ) (k : Fin (n - 1)) (t : ShortField b c) :
    shortBlock hirr n k (sl2Upper t) = shortPosHom n hirr k (.ofAdd (fieldCoord t)) :=
  haveI := finite_shortField (b := b) (c := c)
  (Classical.choose_spec (exists_hom_of_rankOneRels (shortRels n hirr k))).1 t

theorem shortBlock_lower (n : ℕ) (k : Fin (n - 1)) (t : ShortField b c) :
    shortBlock hirr n k (sl2Lower t) = shortNegHom n hirr k (.ofAdd (starCoord t)) :=
  haveI := finite_shortField (b := b) (c := c)
  (Classical.choose_spec (exists_hom_of_rankOneRels (shortRels n hirr k))).2 t

theorem shortBlock_tv01 (n : ℕ) (k : Fin (n - 1)) (t : ShortField b c) :
    shortBlock hirr n k (tv 0 1 t) = shortPosHom n hirr k (.ofAdd (fieldCoord t)) := by
  rw [tv01_eq_sl2Upper, shortBlock_upper]

theorem shortBlock_tv10 (n : ℕ) (k : Fin (n - 1)) (t : ShortField b c) :
    shortBlock hirr n k (tv 1 0 t) = shortNegHom n hirr k (.ofAdd (starCoord t)) := by
  rw [tv10_eq_sl2Lower, shortBlock_lower]

theorem shortBlock_torus (n : ℕ) (k : Fin (n - 1)) (t : (ShortField b c)ˣ) :
    shortBlock hirr n k (torusHom (ShortField b c) t) =
      shortTorusElt n hirr k (fieldCoord (t : ShortField b c)) := by
  have := finite_shortField (b := b) (c := c)
  rw [← shortRels_h n hirr k (t : ShortField b c), RankOneRels.h_def, RankOneRels.w_inv,
    RankOneRels.w_def, RankOneRels.w_def, torusHom_eq_w]
  simp only [map_mul, shortBlock_tv01, shortBlock_tv10, shortRels_x, shortRels_y]
  have h1 : -(-1 : ShortField b c)⁻¹ = 1 := by simp
  rw [h1]

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem four_le_card_shortField' : 4 ≤ Nat.card (ShortField b c) := by
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod]
  nlinarith

theorem shortBlock_injective (h2 : (2 : F) ≠ 0) (n : ℕ) (k : Fin (n - 1)) :
    Function.Injective (shortBlock hirr n k) := by
  have := finite_shortField (b := b) (c := c)
  refine CFSG.Semidihedral.DefiningCharacteristicDimension.nativeSL2_action_injective
    (four_le_card_shortField' (b := b) (c := c)) _ ?_
  have hm : CFSG.Semidihedral.OddFieldSL2.minusIdentity (ShortField b c) =
      torusHom (ShortField b c) (-1) := by
    apply Subtype.ext
    rw [CFSG.Semidihedral.OddFieldSL2.minusIdentity_matrix, coe_torusHom]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
  rw [hm, shortBlock_torus]
  intro h1
  have hfc : fieldCoord (((-1 : (ShortField b c)ˣ)) : ShortField b c) =
      ((-1 : Fˣ) : F) • planeOne := by
    ext j
    fin_cases j <;> simp [fieldCoord, planeOne, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [hfc, ← minusFrame_shortTorus_eq n hirr k (-1), OddFrame.shortTorus_apply] at h1
  have hd := CFSG.LieType.Steinberg.SpinOdd.shortSL2_injective (minusFrame n b c) k true
    (h1.trans (map_one _).symm)
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
    (M : Matrix (Fin 2) (Fin 2) F) 0 0) hd
  simp at this
  exact h2 (by linear_combination -this)

@[expose] def finOne : Fin (3 - 1) := ⟨1, by decide⟩

omit [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem minusLongBlock_tv01 (x : F) :
    minusLongBlock b c (tv 0 1 x) =
      (minusFrame 3 b c).longRoot fin_zero_ne_one true false (.ofAdd x) := by
  rw [minusLongBlock, tv01_eq_upperSL2, HypFrame.longSL2_upperSL2]

omit [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem minusLongBlock_tv10 (x : F) :
    minusLongBlock b c (tv 1 0 x) =
      (minusFrame 3 b c).longRoot fin_zero_ne_one.symm true false (.ofAdd x) := by
  rw [minusLongBlock, tv10_eq_lowerSL2, HypFrame.longSL2_lowerSL2]
  rfl

@[expose] noncomputable def spinNu (b c : F) (t : (ShortField b c)ˣ) : Fˣ :=
  (Units.map (QuadraticAlgebra.norm : ShortField b c →* F) t)⁻¹

@[expose] noncomputable def spinMu (b c : F) (s : Fˣ) : (ShortField b c)ˣ :=
  Units.map (algebraMap F (ShortField b c)).toMonoidHom s⁻¹

omit [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem coe_spinNu (t : (ShortField b c)ˣ) :
    ((spinNu b c t : Fˣ) : F) = (planeNorm b c (fieldCoord (t : ShortField b c)))⁻¹ := by
  rw [spinNu, Units.val_inv_eq_inv_val, Units.coe_map, planeNorm_fieldCoord]

theorem spin_conj_sl (t : (ShortField b c)ˣ) (A : SL(2, F)) :
    shortBlock hirr 3 finOne (torusHom (ShortField b c) t) * minusLongBlock b c A *
        (shortBlock hirr 3 finOne (torusHom (ShortField b c) t))⁻¹ =
      minusLongBlock b c (diagConj2 (spinNu b c t) 1 A) := by
  have ha : fieldCoord (t : ShortField b c) ≠ 0 := fieldCoord_ne_zero t.ne_zero
  have key : (MulAut.conj
      (shortBlock hirr 3 finOne (torusHom (ShortField b c) t))).toMonoidHom.comp
        (minusLongBlock b c) =
      (minusLongBlock b c).comp (diagConj2 (spinNu b c t) 1).toMonoidHom := by
    refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        minusLongBlock_tv01, diagConj2_tv01, shortBlock_torus]
      rw [shortTorusElt_conj_longRoot 3 hirr finOne ha fin_zero_ne_one true false x]
      congr 2
      simp [shortTorusScalar, finOne, coe_spinNu]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        minusLongBlock_tv10, diagConj2_tv10, shortBlock_torus]
      rw [shortTorusElt_conj_longRoot 3 hirr finOne ha fin_zero_ne_one.symm true false x]
      congr 2
      simp [shortTorusScalar, finOne, coe_spinNu, mul_comm]
  exact DFunLike.congr_fun key A

omit [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem starCoord_mul_algebraMap (r : F) (t : ShortField b c) :
    starCoord (t * algebraMap F (ShortField b c) r) = r • starCoord t := by
  ext k
  fin_cases k <;> simp [starCoord, QuadraticAlgebra.algebraMap_eq] <;> ring

omit [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem torusHom_eq_diagSL2 (s : Fˣ) : (torusHom F s : SL(2, F)) = diagSL2 s := rfl

theorem spin_conj_ls (s : Fˣ) (B : SL(2, ShortField b c)) :
    minusLongBlock b c (torusHom F s) * shortBlock hirr 3 finOne B *
        (minusLongBlock b c (torusHom F s))⁻¹ =
      shortBlock hirr 3 finOne (diagConj2 (spinMu b c s) 1 B) := by
  have hT : minusLongBlock b c (torusHom F s) =
      (minusFrame 3 b c).longTorus fin_zero_ne_one true false s := by
    rw [HypFrame.longTorus_apply, torusHom_eq_diagSL2]
    rfl
  have key : (MulAut.conj (minusLongBlock b c (torusHom F s))).toMonoidHom.comp
      (shortBlock hirr 3 finOne) =
      (shortBlock hirr 3 finOne).comp (diagConj2 (spinMu b c s) 1).toMonoidHom := by
    refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        shortBlock_tv01, diagConj2_tv01, hT]
      have h := longTorus_conj_twShortRoot 3 hirr (fin_zero_ne_one) true false s finOne true
        (fieldCoord x)
      simp only [twShortRoot_true] at h
      rw [h]
      congr 3
      simp [longCoroot, finOne, spinMu]
      rw [← map_inv₀, fieldCoord_algebraMap_mul]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        shortBlock_tv10, diagConj2_tv10, hT]
      have h := longTorus_conj_twShortRoot 3 hirr (fin_zero_ne_one) true false s finOne false
        (starCoord x)
      simp only [twShortRoot_false] at h
      rw [h]
      congr 3
      simp [longCoroot, finOne, spinMu, starCoord_mul_algebraMap]
  exact DFunLike.congr_fun key B

@[expose] noncomputable def spinMinusModel :
    TwistedB2Model F (ShortField b c) (spinGroup (quadMinus 3 F b c)) where
  lb := minusLongBlock b c
  sb := shortBlock hirr 3 finOne
  nu := spinNu b c
  mu := spinMu b c
  conj_sl := spin_conj_sl hirr
  conj_ls := spin_conj_ls hirr

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem exists_spinNu_ne (hF : 4 ≤ Nat.card F) : ∃ t, spinNu b c t ≠ (1 : Fˣ) := by
  obtain ⟨r, hr⟩ := exists_unit_sq_ne_one (K := F) hF
  refine ⟨Units.map (algebraMap F (ShortField b c)).toMonoidHom r, fun h => hr ?_⟩
  have h1 := inv_eq_one.mp h
  apply Units.ext
  have := congrArg (fun u : Fˣ => (u : F)) h1
  simpa [QuadraticAlgebra.norm_algebraMap] using this

omit [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] in
theorem exists_spinMu_ne (hF : 3 ≤ Nat.card F) : ∃ s, spinMu b c s ≠ (1 : (ShortField b c)ˣ) := by
  obtain ⟨s, hs⟩ := exists_unit_ne_one (K := F) hF
  refine ⟨s, fun h => hs ?_⟩
  have h1 : Units.map (algebraMap F (ShortField b c)).toMonoidHom s⁻¹ =
      Units.map (algebraMap F (ShortField b c)).toMonoidHom 1 := by rw [map_one]; exact h
  exact inv_eq_one.mp (Units.map_injective (algebraMap F (ShortField b c)).injective h1)

end Short

@[expose] def TwistedB2BlockStandardPair {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {X : Type} [Group X] (W U V : Subgroup X) : Prop :=
  haveI := fact_shortField hirr
  (spinMinusModel hirr).StandardPair W U V

end CFSG.ClassicalInvolution.Models.TwistedPairs
