module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.Unitary
public import CFSG.RankThree.PartOne.CTP.SU4EvenSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.WeakCT.SU4
  CFSG.RankThree.PartOne.CTP.SU4Even
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Universal.Unitary CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CompsPTwoDPairE

section Def

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  (D : KleinDataEven F K σ₀ b c)

include D in
theorem σσ' : ∀ x : K, σ₀.toRingHom (σ₀.toRingHom x) = x := D.σσ

@[expose] def dmat : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-D.δ, D.δ, 1, 1]

@[expose] def dinv : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![-D.ε, D.ε, 1, 1]

theorem dmat_mul_dinv : dmat D * dinv D = 1 := by
  have h1 := D.δ_mul_ε
  rw [dmat, dinv, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> linear_combination h1

theorem su_det (σ : K ≃+* K) (g : SU σ 4) :
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 :=
  (mem_SU.1 g.2).1

@[expose] def suToSL (σ : K ≃+* K) : SU σ 4 →* SL(4, K) where
  toFun g := ⟨((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), su_det σ g⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext rfl

end Def

section Theta

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  (D : KleinDataEven F K σ₀ b c) [Finite F] [CharP F 2]
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def theta : spinGroup (quadMinus 3 F b c) →* SL(4, K) :=
  (conjSL (dmat D) (dinv D) (dmat_mul_dinv D)).toMonoidHom.comp
    ((suToSL σ₀).comp (D.PhiSUEven hirr))

theorem coe_theta (s : spinGroup (quadMinus 3 F b c)) :
    ((theta D hirr s : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      dmat D * D.PhiMon s * dinv D :=
  rfl

theorem theta_lb_upper (x : F) :
    theta D hirr (minusLongBlock b c (tv 0 1 x)) =
      blockSL2 K 3 1 (tv 0 1 (algebraMap F K x)) := by
  refine Subtype.ext ?_
  rw [coe_theta, minusLongBlock_tv01, D.PhiMon_long_e0f1]
  show dmat D * longRootMatrix (1 : Fin 4) (algebraMap F K x * D.ε) * dinv D =
    ((blockSL K 4 2 1 (by omega) (tv 0 1 (algebraMap F K x)) : SL(4, K)) :
      Matrix (Fin 4) (Fin 4) K)
  rw [coe_blockSL_four_one, tv01_eq_sl2Upper]
  have h1 := D.δ_mul_ε
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, dinv, longRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
      CFSG.LieType.Steinberg.coe_sl2Upper] <;>
    first | linear_combination h1 | linear_combination (algebraMap F K x) * h1

theorem theta_lb_lower (x : F) :
    theta D hirr (minusLongBlock b c (tv 1 0 x)) =
      blockSL2 K 3 1 (tv 1 0 (algebraMap F K x)) := by
  refine Subtype.ext ?_
  rw [coe_theta, minusLongBlock_tv10, D.PhiMon_long_e1f0]
  show dmat D * longRootMatrix (2 : Fin 4) (algebraMap F K x * D.δ) * dinv D =
    ((blockSL K 4 2 1 (by omega) (tv 1 0 (algebraMap F K x)) : SL(4, K)) :
      Matrix (Fin 4) (Fin 4) K)
  rw [coe_blockSL_four_one, tv10_eq_sl2Lower]
  have h1 := D.δ_mul_ε
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, dinv, longRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
      CFSG.LieType.Steinberg.coe_sl2Lower] <;>
    first | linear_combination h1 | linear_combination (algebraMap F K x) * h1

theorem theta_comp_lb :
    (theta D hirr).comp (minusLongBlock b c) =
      (blockSL2 K 3 1).comp (Matrix.SpecialLinearGroup.map (algebraMap F K)) := by
  refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, theta_lb_upper]
    congr 1
    refine Subtype.ext ?_
    rw [tv01_eq_sl2Upper, tv01_eq_sl2Upper]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.SpecialLinearGroup.map_apply_coe]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, theta_lb_lower]
    congr 1
    refine Subtype.ext ?_
    rw [tv10_eq_sl2Lower, tv10_eq_sl2Lower]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Steinberg.coe_sl2Lower, Matrix.SpecialLinearGroup.map_apply_coe]

section Sb

variable [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

@[expose] def kup (t : ShortField b c) : K :=
  D.δ * (algebraMap F K t.re - algebraMap F K t.im * D.ω)

@[expose] def klow (t : ShortField b c) : K :=
  D.ε * (algebraMap F K t.re - algebraMap F K t.im * D.ω)

theorem theta_sb_upper (t : ShortField b c) :
    theta D hirr (shortBlock hirr 3 finOne (tv 0 1 t)) =
      usbSL σ₀.toRingHom (σσ' D) (tv 0 1 (kup D t)) := by
  refine Subtype.ext ?_
  rw [coe_theta, shortBlock_tv01]
  change dmat D * D.PhiMon (twShortRoot 3 hirr iO true (.ofAdd (fieldCoord t))) * dinv D = _
  rw [D.PhiMon_short_e1 hirr (fieldCoord t), coe_usbSL, tv01_eq_sl2Upper]
  have h1 := D.δ_mul_ε
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, dinv, rootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
      CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.single_apply, fieldCoord, kup] <;>
    first | ring1 | linear_combination h1 |
      linear_combination (D.δ * (algebraMap F K t.re - algebraMap F K t.im * D.ω)) * h1 |
      linear_combination (D.ε * (algebraMap F K t.re - algebraMap F K t.im * D.ω)) * h1

theorem theta_sb_lower (t : ShortField b c) :
    theta D hirr (shortBlock hirr 3 finOne (tv 1 0 t)) =
      usbSL σ₀.toRingHom (σσ' D) (tv 1 0 (klow D t)) := by
  refine Subtype.ext ?_
  rw [coe_theta, shortBlock_tv10]
  change dmat D * D.PhiMon (twShortRoot 3 hirr iO false (.ofAdd (starCoord t))) * dinv D = _
  rw [D.PhiMon_short_f1 hirr (starCoord t), coe_usbSL, tv10_eq_sl2Lower]
  have h1 := D.δ_mul_ε
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, dinv, rootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal,
      CFSG.LieType.Steinberg.coe_sl2Lower, Matrix.single_apply, starCoord, klow] <;>
    first | ring1 | linear_combination h1 |
      linear_combination (D.δ * (algebraMap F K t.re - algebraMap F K t.im * D.ω)) * h1 |
      linear_combination (D.ε * (algebraMap F K t.re - algebraMap F K t.im * D.ω)) * h1

end Sb

section Range

variable [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

theorem range_theta_sb :
    ((theta D hirr).comp (shortBlock hirr 3 finOne)).range =
      (usbSL σ₀.toRingHom (σσ' D)).range := by
  have h1 := D.δ_mul_ε
  apply le_antisymm
  · rintro _ ⟨B, rfl⟩
    refine sl2_mem_of_tv ((theta D hirr).comp (shortBlock hirr 3 finOne))
      (H := (usbSL σ₀.toRingHom (σσ' D)).range) (fun t => ?_) (fun t => ?_) B
    · rw [MonoidHom.comp_apply, theta_sb_upper]
      exact ⟨_, rfl⟩
    · rw [MonoidHom.comp_apply, theta_sb_lower]
      exact ⟨_, rfl⟩
  · rintro _ ⟨B, rfl⟩
    refine sl2_mem_of_tv (usbSL σ₀.toRingHom (σσ' D))
      (H := ((theta D hirr).comp (shortBlock hirr 3 finOne)).range) (fun y => ?_) (fun y => ?_) B
    · obtain ⟨u, v, huv⟩ := D.span (y * D.ε)
      refine ⟨tv 0 1 (⟨u, v⟩ : ShortField b c), ?_⟩
      rw [MonoidHom.comp_apply, theta_sb_upper]
      have hk : kup D (⟨u, v⟩ : ShortField b c) = y := by
        show D.δ * (algebraMap F K u - algebraMap F K v * D.ω) = y
        rw [← huv]
        linear_combination y * h1
      rw [hk]
    · obtain ⟨u, v, huv⟩ := D.span (y * D.δ)
      refine ⟨tv 1 0 (⟨u, v⟩ : ShortField b c), ?_⟩
      rw [MonoidHom.comp_apply, theta_sb_lower]
      have hk : klow D (⟨u, v⟩ : ShortField b c) = y := by
        show D.ε * (algebraMap F K u - algebraMap F K v * D.ω) = y
        rw [← huv]
        linear_combination y * h1
      rw [hk]

end Range

end Theta

end CompsPTwoDPairE

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
