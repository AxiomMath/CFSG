module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZHolds
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Y
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Unitary

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld Matrix
open scoped MatrixGroups Matrix

variable {K : Type} [Field K]

private def blockSix (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 6) (Fin 6) K :=
  !![g 0 0, g 0 1, 0, 0, 0, 0;
     g 1 0, g 1 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, g 1 1, g 1 0;
     0, 0, 0, 0, g 0 1, g 0 0]

private def blockFour (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, g 1 1, g 1 0;
     0, 0, g 0 1, g 0 0]

private def reflect2 (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![g 1 1, g 1 0; g 0 1, g 0 0]

private theorem blockSix_one : blockSix (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockSix, Matrix.one_apply]

private theorem blockSix_mul (g h : Matrix (Fin 2) (Fin 2) K) :
    blockSix (g * h) = blockSix g * blockSix h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockSix, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_two] <;> ring

private theorem blockFour_reindex (g : Matrix (Fin 2) (Fin 2) K) :
    blockFour g = Matrix.reindexAlgEquiv K K (finSumFinEquiv : Sum (Fin 2) (Fin 2) ≃ Fin 4)
      (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 (reflect2 g)) := by
  have h0 : (Fin.addCases Sum.inl Sum.inr (0 : Fin 4) : Sum (Fin 2) (Fin 2)) = Sum.inl 0 := by
    decide
  have h1 : (Fin.addCases Sum.inl Sum.inr (1 : Fin 4) : Sum (Fin 2) (Fin 2)) = Sum.inl 1 := by
    decide
  have h2 : (Fin.addCases Sum.inl Sum.inr (2 : Fin 4) : Sum (Fin 2) (Fin 2)) = Sum.inr 0 := by
    decide
  have h3 : (Fin.addCases Sum.inl Sum.inr (3 : Fin 4) : Sum (Fin 2) (Fin 2)) = Sum.inr 1 := by
    decide
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockFour, reflect2, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv, h0, h1, h2, h3, Matrix.fromBlocks]

private theorem det_reflect2 (g : Matrix (Fin 2) (Fin 2) K) : (reflect2 g).det = g.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp [reflect2]
  ring

private theorem det_blockFour (g : Matrix (Fin 2) (Fin 2) K) : (blockFour g).det = g.det := by
  rw [blockFour_reindex, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁]
  simp [det_reflect2]

private theorem blockSix_reindex (g : Matrix (Fin 2) (Fin 2) K) :
    blockSix g = Matrix.reindexAlgEquiv K K (finSumFinEquiv : Sum (Fin 2) (Fin 4) ≃ Fin 6)
      (Matrix.fromBlocks g 0 0 (blockFour g)) := by
  have h0 : (Fin.addCases Sum.inl Sum.inr (0 : Fin 6) : Sum (Fin 2) (Fin 4)) = Sum.inl 0 := by
    decide
  have h1 : (Fin.addCases Sum.inl Sum.inr (1 : Fin 6) : Sum (Fin 2) (Fin 4)) = Sum.inl 1 := by
    decide
  have h2 : (Fin.addCases Sum.inl Sum.inr (2 : Fin 6) : Sum (Fin 2) (Fin 4)) = Sum.inr 0 := by
    decide
  have h3 : (Fin.addCases Sum.inl Sum.inr (3 : Fin 6) : Sum (Fin 2) (Fin 4)) = Sum.inr 1 := by
    decide
  have h4 : (Fin.addCases Sum.inl Sum.inr (4 : Fin 6) : Sum (Fin 2) (Fin 4)) = Sum.inr 2 := by
    decide
  have h5 : (Fin.addCases Sum.inl Sum.inr (5 : Fin 6) : Sum (Fin 2) (Fin 4)) = Sum.inr 3 := by
    decide
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockSix, blockFour, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply, finSumFinEquiv, h0, h1, h2, h3, h4, h5, Matrix.fromBlocks]

private theorem det_blockSix (g : Matrix (Fin 2) (Fin 2) K) : (blockSix g).det = g.det ^ 2 := by
  rw [blockSix_reindex, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, det_blockFour]
  ring

private def blockSixSL (g : SL2 K) : SL(6, K) :=
  ⟨blockSix (g : Matrix (Fin 2) (Fin 2) K), by rw [det_blockSix, g.2, one_pow]⟩

private theorem e6_orbitMin_zero :
    TwistTag.E6.orbitMin aSixteen = (0 : Fin TwistTag.E6.tag.rank) := by decide +kernel

private theorem e6_perm_zero :
    TwistTag.E6.perm (0 : Fin TwistTag.E6.tag.rank) = (5 : Fin TwistTag.E6.tag.rank) := by
  decide +kernel

private theorem e6_orbit_zero_card : (TwistTag.E6.orbit aSixteen).card = 2 := by decide +kernel

private theorem a5Node_zero : a5Node (0 : Fin 5) = (0 : Fin TwistTag.E6.tag.rank) := rfl

private theorem a5Node_two : a5Node (2 : Fin 5) = (3 : Fin TwistTag.E6.tag.rank) := rfl

private theorem a5Node_four : a5Node (4 : Fin 5) = (5 : Fin TwistTag.E6.tag.rank) := rfl

private theorem e6Flat_one_eq : e6Flat (f4Word 1) = [a5Node (1 : Fin 5), a5Node (3 : Fin 5)] := by
  decide +kernel

private theorem e6Flat_two_eq : e6Flat (f4Word 2) =
    [a5Node (0 : Fin 5), a5Node (4 : Fin 5), a5Node (1 : Fin 5), a5Node (3 : Fin 5)] := by
  decide +kernel

private theorem eTw_zero (ε : K) : eTw ε (0 : Fin 5) = -1 := rfl

private theorem eTw_four (ε : K) : eTw ε (4 : Fin 5) = 1 := rfl

private theorem coe_orbitX_zero [Finite K] (σ : K →+* K) (c : orbitField TwistTag.E6 K σ aSixteen) :
    (orbitX TwistTag.E6 K σ aSixteen c : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K (0 : Fin TwistTag.E6.tag.rank) (c : K) *
        xUnit TwistTag.E6.tag K (5 : Fin TwistTag.E6.tag.rank) (σ (c : K)) := by
  have h := coe_orbitX_two (K := K) (σ := σ) (a := aSixteen) e6_orbit_zero_card c
  rwa [e6_orbitMin_zero, e6_perm_zero] at h

private theorem coe_orbitY_zero [Finite K] (σ : K →+* K) (c : orbitField TwistTag.E6 K σ aSixteen) :
    (orbitY TwistTag.E6 K σ aSixteen c : ModGL TwistTag.E6.tag K) =
      yUnit TwistTag.E6.tag K (0 : Fin TwistTag.E6.tag.rank) (c : K) *
        yUnit TwistTag.E6.tag K (5 : Fin TwistTag.E6.tag.rank) (σ (c : K)) := by
  have h := coe_orbitY_two (K := K) (σ := σ) (a := aSixteen) e6_orbit_zero_card c
  rwa [e6_orbitMin_zero, e6_perm_zero] at h

private theorem torusUnit_coe {k : Type} [Field k] [Finite k] [Algebra k K] [Finite K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) :
    ((torusUnit σ hσ hK t : (orbitField TwistTag.E6 K σ.toRingHom aSixteen)) : K) = (t : K) := rfl

private theorem torusWord_eq_orbitH {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) :
    (torusWord σ hσ hK t : ModGL TwistTag.E6.tag K) =
      (orbitH TwistTag.E6 K σ.toRingHom aSixteen (torusUnit σ hσ hK t) :
        ModGL TwistTag.E6.tag K) := by
  change ((List.finRange TwistTag.E6.foldedTag.rank).map fun a =>
      (orbitH TwistTag.E6 K σ.toRingHom a (torusW σ hσ hK t a) : ModGL TwistTag.E6.tag K)).prod = _
  exact list_prod_orbitH_mulSingle (t := TwistTag.E6) (K := K) (σ := σ.toRingHom)
    aSixteen (torusUnit σ hσ hK t)

private theorem torusUnit_one {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) :
    torusUnit σ hσ hK (1 : Kˣ) = 1 := by
  ext
  rfl

theorem coe_iota_f4Z (k K : Type) [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2) :
    ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (weylWord K (e6Flat (f4Word 0)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word 0)))⁻¹) *
      ((weylWord K (e6Flat (f4Word 1)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word 1)))⁻¹) *
      (weylWord K (e6Flat (f4Word 2)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word 2)))⁻¹)) := by
  have hcoe : ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap k K) (thetaE6 k ⟨f4Z k, f4Z_mem_adjointGroup⟩) := rfl
  have hS : baseChangeGL (algebraMap k K) (xUnit TwistTag.E6.tag k e6Three 1 *
      yUnit TwistTag.E6.tag k e6Three (-3)) =
      xUnit TwistTag.E6.tag K e6Three 1 * yUnit TwistTag.E6.tag K e6Three (-3) := by
    rw [map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit, map_one, map_neg, map_ofNat]
  have hW : ∀ i : Fin 3, baseChangeGL (algebraMap k K)
      (weylWord k (e6Flat (f4Word i)) * (xUnit TwistTag.E6.tag k e6Three 1 *
        yUnit TwistTag.E6.tag k e6Three (-3)) * (weylWord k (e6Flat (f4Word i)))⁻¹) =
      weylWord K (e6Flat (f4Word i)) * (xUnit TwistTag.E6.tag K e6Three 1 *
        yUnit TwistTag.E6.tag K e6Three (-3)) * (weylWord K (e6Flat (f4Word i)))⁻¹ := fun i => by
    rw [map_mul, map_mul, map_inv, baseChangeGL_weylWord, hS]
  have e3 : ∀ a b c : ModGL TwistTag.E6.tag k, baseChangeGL (algebraMap k K) (a * (b * c)) =
      baseChangeGL (algebraMap k K) a *
        (baseChangeGL (algebraMap k K) b * baseChangeGL (algebraMap k K) c) :=
    fun a b c => by rw [map_mul, map_mul]
  rw [hcoe, thetaE6_f4Z, e3, hW 0, hW 1, hW 2]

private def wSL (s : Fin 5) (c : K) : SL(6, K) :=
  tv s.castSucc s.succ c * tv s.succ s.castSucc (-c⁻¹) * tv s.castSucc s.succ c

private def zR (ε : K) : SL(6, K) :=
  tv (2 : Fin 6) 3 ε⁻¹ * tv (3 : Fin 6) 2 (-3 * ε)

private def zW1 : SL(6, K) := wSL (1 : Fin 5) (-1) * wSL (3 : Fin 5) 1

private def zW2 : SL(6, K) :=
  wSL (0 : Fin 5) (-1) * wSL (4 : Fin 5) 1 * wSL (1 : Fin 5) (-1) * wSL (3 : Fin 5) 1

private def zW1mat : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 1]

private def zW2mat : Matrix (Fin 6) (Fin 6) K :=
  !![0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 1, 0, 0]

private def zR1 (ε : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     0, -2, 0, 0, ε⁻¹, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, -3 * ε, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private def zR2 (ε : K) : Matrix (Fin 6) (Fin 6) K :=
  !![ -2, 0, 0, 0, 0, ε⁻¹;
      0, 1, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      -3 * ε, 0, 0, 0, 0, 1]

private def zSix (ε : K) : SL(6, K) :=
  zR ε * (zW1 * zR ε * zW1⁻¹ * (zW2 * zR ε * zW2⁻¹))

private def zSixMat (ε : K) : Matrix (Fin 6) (Fin 6) K :=
  !![ -2, 0, 0, 0, 0, ε⁻¹;
      0, -2, 0, 0, ε⁻¹, 0;
      0, 0, -2, ε⁻¹, 0, 0;
      0, 0, -3 * ε, 1, 0, 0;
      0, -3 * ε, 0, 0, 1, 0;
      -3 * ε, 0, 0, 0, 0, 1]

private def DW (u su : K) : SL(6, K) :=
  (tv (0 : Fin 6) 1 (-u) * tv (4 : Fin 6) 5 su) *
    (tv (1 : Fin 6) 0 u⁻¹ * tv (5 : Fin 6) 4 (-su⁻¹)) *
      (tv (0 : Fin 6) 1 (-u) * tv (4 : Fin 6) 5 su)

private def dwMat (u su : K) : Matrix (Fin 6) (Fin 6) K :=
  !![0, -u, 0, 0, 0, 0;
     u⁻¹, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, su;
     0, 0, 0, 0, -su⁻¹, 0]

private def dSix (t : Kˣ) : SL(6, K) :=
  ⟨Matrix.diagonal ![((t : K)), (((t⁻¹ : Kˣ) : K)), 1, 1, (((t⁻¹ : Kˣ) : K)), ((t : K))], by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_six, Units.val_inv_eq_inv_val]⟩

private def wSL1m : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private def wSL3m : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 1]

private def wSL0m : Matrix (Fin 6) (Fin 6) K :=
  !![0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private def wSL4m : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 0]

private theorem coe_wSL1m :
    ((wSL (1 : Fin 5) (-1) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = wSL1m := by
  rw [wSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSL1m, tv, Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

private theorem coe_wSL3m :
    ((wSL (3 : Fin 5) 1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = wSL3m := by
  rw [wSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSL3m, tv, Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

private theorem coe_wSL0m :
    ((wSL (0 : Fin 5) (-1) : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = wSL0m := by
  rw [wSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSL0m, tv, Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

private theorem coe_wSL4m :
    ((wSL (4 : Fin 5) 1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = wSL4m := by
  rw [wSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSL4m, tv, Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

private theorem coe_zW1 : ((zW1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = zW1mat := by
  rw [zW1, Matrix.SpecialLinearGroup.coe_mul, coe_wSL1m, coe_wSL3m, zW1mat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSL1m, wSL3m, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

private theorem coe_zW2 : ((zW2 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = zW2mat := by
  rw [zW2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_wSL0m, coe_wSL4m, coe_wSL1m, coe_wSL3m, zW2mat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSL0m, wSL4m, wSL1m, wSL3m, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply]

private theorem coe_zR (ε : K) :
    ((zR ε : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.transvection (2 : Fin 6) 3 ε⁻¹ *
        Matrix.transvection (3 : Fin 6) 2 (-3 * ε) := by
  rw [zR, Matrix.SpecialLinearGroup.coe_mul,
    tv_of_ne (by decide : (2 : Fin 6) ≠ 3), tv_of_ne (by decide : (3 : Fin 6) ≠ 2),
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rfl

private theorem coe_zRW1 (ε : K) (hε : ε ≠ 0) :
    ((zW1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        ((zR ε : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      zR1 ε * ((zW1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) := by
  rw [coe_zW1, coe_zR, zR1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zW1mat, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply, mul_inv_cancel₀ hε, inv_mul_cancel₀ hε] <;>
    field_simp [hε] <;> ring

private theorem coe_zRW2 (ε : K) (hε : ε ≠ 0) :
    ((zW2 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        ((zR ε : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      zR2 ε * ((zW2 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) := by
  rw [coe_zW2, coe_zR, zR2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zW2mat, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply, mul_inv_cancel₀ hε, inv_mul_cancel₀ hε] <;>
    field_simp [hε] <;> ring

private theorem coe_zR1 (ε : K) (hε : ε ≠ 0) :
    (((zW1 * zR ε * zW1⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K) = zR1 ε := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hW : ((zW1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
      (((zW1⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have h : ((zW1 * zW1⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [mul_inv_cancel]
      rfl
    rwa [Matrix.SpecialLinearGroup.coe_mul] at h
  calc (((zW1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        ((zR ε : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)) *
        (((zW1⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K)
      = (zR1 ε * ((zW1 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)) *
        (((zW1⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K) := by rw [coe_zRW1 ε hε]
    _ = zR1 ε := by rw [Matrix.mul_assoc, hW, Matrix.mul_one]

private theorem coe_zR2 (ε : K) (hε : ε ≠ 0) :
    (((zW2 * zR ε * zW2⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K) = zR2 ε := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hW : ((zW2 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
      (((zW2⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    have h : ((zW2 * zW2⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [mul_inv_cancel]
      rfl
    rwa [Matrix.SpecialLinearGroup.coe_mul] at h
  calc (((zW2 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        ((zR ε : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)) *
        (((zW2⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K)
      = (zR2 ε * ((zW2 : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)) *
        (((zW2⁻¹ : SL(6, K))) : Matrix (Fin 6) (Fin 6) K) := by rw [coe_zRW2 ε hε]
    _ = zR2 ε := by rw [Matrix.mul_assoc, hW, Matrix.mul_one]

private theorem coe_zSix (ε : K) (hε : ε ≠ 0) :
    ((zSix ε : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = zSixMat ε := by
  rw [zSix, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_zR1 ε hε, coe_zR2 ε hε,
    coe_zR, zSixMat, zR1, zR2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply, mul_inv_cancel₀ hε, inv_mul_cancel₀ hε] <;>
    field_simp [hε] <;> ring

private def dwMatInv : Matrix (Fin 6) (Fin 6) K :=
  !![0, 1, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0]

private theorem dwMat_one_mul_inv : dwMat (1 : K) 1 * dwMatInv (K := K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dwMat, dwMatInv, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply]

private theorem coe_DW (u su : K) (hu : u ≠ 0) (hsu : su ≠ 0) :
    ((DW u su : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = dwMat u su := by
  rw [DW, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dwMat, tv, Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply] <;>
    field_simp [hu, hsu] <;> ring <;> simp

private theorem map_zR (σ : K →+* K) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) {ε : K}
    (hΨ : IsPsiTw σ ε Ψ) (hε0 : ε ≠ 0) :
    Ψ (zR ε) = xUnit TwistTag.E6.tag K e6Three 1 *
      yUnit TwistTag.E6.tag K e6Three (-3) := by
  rw [zR, map_mul]
  change Ψ (tv (Fin.castSucc (2 : Fin 5)) (Fin.succ (2 : Fin 5)) ε⁻¹) *
      Ψ (tv (Fin.succ (2 : Fin 5)) (Fin.castSucc (2 : Fin 5)) (-3 * ε)) =
    xUnit TwistTag.E6.tag K e6Three 1 * yUnit TwistTag.E6.tag K e6Three (-3)
  rw [hΨ.upper (2 : Fin 5) (ε⁻¹), hΨ.lower (2 : Fin 5) (-3 * ε)]
  have h1 : eTw ε (2 : Fin 5) * ε⁻¹ = 1 := by
    rw [show eTw ε (2 : Fin 5) = ε from rfl, mul_inv_cancel₀ hε0]
  have h2 : (eTw ε (2 : Fin 5))⁻¹ * (-3 * ε) = -3 := by
    rw [show eTw ε (2 : Fin 5) = ε from rfl]
    field_simp [hε0]
  rw [h1, h2]
  simp [a5Node_two, e6Three]
  rfl

private theorem map_wSL (σ : K →+* K) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) {ε : K}
    (hΨ : IsPsiTw σ ε Ψ) (hε0 : ε ≠ 0) (s : Fin 5) :
    Ψ (wSL s (eTw ε s)⁻¹) = weylElt TwistTag.E6.tag K (a5Node s) 1 := by
  have he0 : eTw ε s ≠ 0 := by
    fin_cases s <;> simp [eTw, hε0]
  rw [wSL, map_mul, map_mul, hΨ.upper s ((eTw ε s)⁻¹), hΨ.lower s (-((eTw ε s)⁻¹)⁻¹)]
  rw [show eTw ε s * (eTw ε s)⁻¹ = 1 from mul_inv_cancel₀ he0]
  rw [show (eTw ε s)⁻¹ * -((eTw ε s)⁻¹)⁻¹ = -1 by
    rw [inv_inv, mul_neg, inv_mul_cancel₀ he0]]
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

private theorem map_zW1 (σ : K →+* K) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) {ε : K}
    (hΨ : IsPsiTw σ ε Ψ) (hε0 : ε ≠ 0) :
    Ψ (zW1 : SL(6, K)) = weylWord K (e6Flat (f4Word 1)) := by
  rw [zW1, map_mul]
  rw [show wSL (1 : Fin 5) (-1) = wSL (1 : Fin 5) (eTw ε (1 : Fin 5))⁻¹ by
        simp [eTw],
    show wSL (3 : Fin 5) 1 = wSL (3 : Fin 5) (eTw ε (3 : Fin 5))⁻¹ by simp [eTw]]
  rw [map_wSL σ Ψ hΨ hε0 (1 : Fin 5), map_wSL σ Ψ hΨ hε0 (3 : Fin 5),
    e6Flat_one_eq, weylWord_cons, weylWord_cons, weylWord_nil, mul_one]

private theorem map_zW2 (σ : K →+* K) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) {ε : K}
    (hΨ : IsPsiTw σ ε Ψ) (hε0 : ε ≠ 0) :
    Ψ (zW2 : SL(6, K)) = weylWord K (e6Flat (f4Word 2)) := by
  rw [zW2, map_mul, map_mul, map_mul]
  rw [show wSL (0 : Fin 5) (-1) = wSL (0 : Fin 5) (eTw ε (0 : Fin 5))⁻¹ by
        simp [eTw],
    show wSL (4 : Fin 5) 1 = wSL (4 : Fin 5) (eTw ε (4 : Fin 5))⁻¹ by simp [eTw],
    show wSL (1 : Fin 5) (-1) = wSL (1 : Fin 5) (eTw ε (1 : Fin 5))⁻¹ by simp [eTw],
    show wSL (3 : Fin 5) 1 = wSL (3 : Fin 5) (eTw ε (3 : Fin 5))⁻¹ by simp [eTw]]
  rw [map_wSL σ Ψ hΨ hε0 (0 : Fin 5), map_wSL σ Ψ hΨ hε0 (4 : Fin 5),
    map_wSL σ Ψ hΨ hε0 (1 : Fin 5), map_wSL σ Ψ hΨ hε0 (3 : Fin 5),
    e6Flat_two_eq, weylWord_cons, weylWord_cons, weylWord_cons, weylWord_cons,
    weylWord_nil, mul_one]
  group

private theorem map_zSix (k K : Type) [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) {ε : K}
    (hΨ : IsPsiTw σ.toRingHom ε Ψ) (hε0 : ε ≠ 0) :
    Ψ (zSix ε) = ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
  rw [coe_iota_f4Z k K σ hfix hK]
  simp only [zSix, map_mul, map_inv]
  rw [map_zR σ.toRingHom Ψ hΨ hε0, map_zW1 σ.toRingHom Ψ hΨ hε0,
    map_zW2 σ.toRingHom Ψ hΨ hε0, e6Flat_zero, weylWord_nil]
  group

private theorem map_DW_eq_orbitN [Finite K] (σ : K →+* K) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K)
    {ε : K} (hΨ : IsPsiTw σ ε Ψ) (t : Kˣ) (htσ : σ (t : K) = (t : K)⁻¹)
    (u : (orbitField TwistTag.E6 K σ aSixteen)ˣ) (hu : (u : K) = (t : K)) :
    Ψ (DW (t : K) (σ (t : K))) =
      (orbitN TwistTag.E6 K σ aSixteen u : ModGL TwistTag.E6.tag K) := by
  rw [DW]
  simp only [map_mul]
  have hx0 : Ψ (tv (0 : Fin 6) 1 (-(t : K))) =
      xUnit TwistTag.E6.tag K (0 : Fin TwistTag.E6.tag.rank) (t : K) := by
    have h := hΨ.upper (0 : Fin 5) (-(t : K))
    simpa [a5Node_zero, eTw_zero] using h
  have hx4 : Ψ (tv (4 : Fin 6) 5 (σ (t : K))) =
      xUnit TwistTag.E6.tag K (a5Node (4 : Fin 5)) (σ (t : K)) := by
    have h := hΨ.upper (4 : Fin 5) (σ (t : K))
    simpa [eTw_four] using h
  have hy0 : Ψ (tv (1 : Fin 6) 0 ((t : K)⁻¹)) =
      yUnit TwistTag.E6.tag K (0 : Fin TwistTag.E6.tag.rank) (-(t : K)⁻¹) := by
    have h := hΨ.lower (0 : Fin 5) ((t : K)⁻¹)
    simpa [a5Node_zero, eTw_zero] using h
  have hy4 : Ψ (tv (5 : Fin 6) 4 (-(σ (t : K))⁻¹)) =
      yUnit TwistTag.E6.tag K (a5Node (4 : Fin 5)) (-(σ (t : K))⁻¹) := by
    have h := hΨ.lower (4 : Fin 5) (-(σ (t : K))⁻¹)
    simpa [eTw_four] using h
  rw [hx0, hx4, hy0, hy4]
  let c : orbitField TwistTag.E6 K σ aSixteen :=
    -(((u⁻¹ : (orbitField TwistTag.E6 K σ aSixteen)ˣ) :
      (orbitField TwistTag.E6 K σ aSixteen)))
  have horbit : (orbitN TwistTag.E6 K σ aSixteen u : ModGL TwistTag.E6.tag K) =
      (orbitX TwistTag.E6 K σ aSixteen (u : orbitField TwistTag.E6 K σ aSixteen) :
        ModGL TwistTag.E6.tag K) *
      (orbitY TwistTag.E6 K σ aSixteen c : ModGL TwistTag.E6.tag K) *
      (orbitX TwistTag.E6 K σ aSixteen (u : orbitField TwistTag.E6 K σ aSixteen) :
        ModGL TwistTag.E6.tag K) := rfl
  rw [horbit, coe_orbitX_zero σ (u : orbitField TwistTag.E6 K σ aSixteen),
    coe_orbitY_zero σ c]
  simp only [c, hu, htσ, a5Node_zero, a5Node_four, map_neg, map_inv₀, inv_inv,
    Units.val_inv_eq_inv_val, Subfield.coe_neg, Subfield.coe_inv, neg_inj]

private theorem det_dwMat_one : (dwMat (1 : K) 1).det = 1 := by
  rw [← coe_DW 1 1 (by norm_num) (by norm_num)]
  exact (DW 1 1).2

private theorem det_dwMatInv : (dwMatInv (K := K)).det = 1 := by
  have h := congrArg Matrix.det (dwMat_one_mul_inv (K := K))
  rw [Matrix.det_mul, det_dwMat_one, Matrix.det_one] at h
  simpa using h

private def dwInvSL : SL(6, K) := ⟨dwMatInv (K := K), det_dwMatInv⟩

private theorem coe_dwInvSL : ((dwInvSL : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = dwMatInv := rfl

private theorem DW_one_mul_dwInvSL : (DW 1 1 : SL(6, K)) * dwInvSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_DW 1 1 (by norm_num) (by norm_num),
    coe_dwInvSL, dwMat_one_mul_inv]
  rfl

private theorem DW_one_inv_eq : ((DW 1 1 : SL(6, K))⁻¹) = dwInvSL := by
  rw [eq_comm, inv_eq_of_mul_eq_one_right DW_one_mul_dwInvSL]

private theorem dSix_eq (t : Kˣ) :
    ((dSix t : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      ((DW (t : K) (t : K)⁻¹ * (DW 1 1)⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) := by
  rw [dSix]
  change Matrix.diagonal ![((t : K)), (((t⁻¹ : Kˣ) : K)), 1, 1, (((t⁻¹ : Kˣ) : K)), ((t : K))] =
    ((DW (t : K) (t : K)⁻¹ * (DW 1 1)⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_DW (t : K) (t : K)⁻¹ t.ne_zero (inv_ne_zero t.ne_zero),
    DW_one_inv_eq, coe_dwInvSL, dwMat, dwMatInv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.diagonal,
      Units.val_inv_eq_inv_val, mul_inv_cancel₀ t.ne_zero]

private theorem blockSix_mul_zSix (g : Matrix (Fin 2) (Fin 2) K) (ε : K) :
    blockSix g * zSixMat ε = zSixMat ε * blockSix g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockSix, zSixMat, Matrix.mul_apply, Fin.sum_univ_six] <;> ring

private theorem dSix_eq_SL (t : Kˣ) :
    dSix t = DW (t : K) (t : K)⁻¹ * (DW 1 1)⁻¹ :=
  Subtype.ext (dSix_eq t)

private theorem blockSixSL_mem_unitarySL (σ : K →+* K) (hσ : ∀ c, σ (σ c) = c) (g : SL2 K)
    (hg : (((g : Matrix (Fin 2) (Fin 2) K).map σ)ᵀ * (g : Matrix (Fin 2) (Fin 2) K)) = 1) :
    blockSixSL g ∈ unitarySL σ := by
  have h00 : σ (g 0 0) * g 0 0 + σ (g 1 0) * g 1 0 = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
  have h01 : σ (g 0 0) * g 0 1 + σ (g 1 0) * g 1 1 = 0 := by
    have := congrFun (congrFun hg 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
  have h10 : σ (g 0 1) * g 0 0 + σ (g 1 1) * g 1 0 = 0 := by
    have := congrFun (congrFun hg 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
  have h11 : σ (g 0 1) * g 0 1 + σ (g 1 1) * g 1 1 = 1 := by
    have := congrFun (congrFun hg 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
  rw [mem_unitarySL_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockSixSL, blockSix, antiId, Matrix.mul_apply, Fin.sum_univ_six, Matrix.map_apply,
      Matrix.one_apply, h00, h01, h10, h11] <;> ring
  all_goals first
    | linear_combination h10
    | linear_combination h01
    | linear_combination h00
    | linear_combination h11

private def suX (β : Kˣ) (c : K) : SL2 K :=
  ⟨!![1 + c, -c * ((β : K))⁻¹; c * ((β : K)), 1 - c], by
    rw [Matrix.det_fin_two]
    change (1 + c) * (1 - c) - (-c * ((β : K))⁻¹) * (c * (β : K)) = 1
    have hβ0 : (β : K) ≠ 0 := β.ne_zero
    field_simp
    ring⟩

private def suY (β : Kˣ) (c : K) : SL2 K :=
  ⟨!![1 - c, c * ((β : K)); -c * ((β : K))⁻¹, 1 + c], by
    rw [Matrix.det_fin_two]
    change (1 - c) * (1 + c) - (c * (β : K)) * (-c * ((β : K))⁻¹) = 1
    have hβ0 : (β : K) ≠ 0 := β.ne_zero
    field_simp
    ring⟩

private def uX (β : Kˣ) (c : K) : SL(6, K) := blockSixSL (suX β c)

private def uY (β : Kˣ) (c : K) : SL(6, K) := blockSixSL (suY β c)

private theorem uX_mem_unitarySL (β : Kˣ) (c : K) (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (hβ : σ (β : K) = -((β : K))⁻¹) (hc : σ c = -c) :
    uX β c ∈ unitarySL σ := by
  apply blockSixSL_mem_unitarySL σ hσ (suX β c)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hβ, hc] <;>
    field_simp [show (β : K) ≠ 0 from β.ne_zero] <;> ring

private theorem uY_mem_unitarySL (β : Kˣ) (c : K) (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (hβ : σ (β : K) = -((β : K))⁻¹) (hc : σ c = -c) :
    uY β c ∈ unitarySL σ := by
  apply blockSixSL_mem_unitarySL σ hσ (suY β c)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hβ, hc] <;>
    field_simp [show (β : K) ≠ 0 from β.ne_zero] <;> ring

private theorem coe_uX (β : Kˣ) (c : K) :
    ((uX β c : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      blockSix (suX β c : Matrix (Fin 2) (Fin 2) K) := rfl

private theorem coe_uY (β : Kˣ) (c : K) :
    ((uY β c : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      blockSix (suY β c : Matrix (Fin 2) (Fin 2) K) := rfl

private theorem uX_mul_zSix (β : Kˣ) (c ε : K) (hε : ε ≠ 0) :
    uX β c * zSix ε = zSix ε * uX β c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uX,
    coe_zSix ε hε]
  exact blockSix_mul_zSix (suX β c : Matrix (Fin 2) (Fin 2) K) ε

private theorem uY_mul_zSix (β : Kˣ) (c ε : K) (hε : ε ≠ 0) :
    uY β c * zSix ε = zSix ε * uY β c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uY,
    coe_zSix ε hε]
  exact blockSix_mul_zSix (suY β c : Matrix (Fin 2) (Fin 2) K) ε

private theorem suX_mul_add (β : Kˣ) (c d : K) : suX β c * suX β d = suX β (c + d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suX, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [show (β : K) ≠ 0 from β.ne_zero] <;> ring

private theorem suY_mul_add (β : Kˣ) (c d : K) : suY β c * suY β d = suY β (c + d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suY, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [show (β : K) ≠ 0 from β.ne_zero] <;> ring

private theorem suX_zero (β : Kˣ) : suX β 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suX, Matrix.one_apply]

private theorem suY_zero (β : Kˣ) : suY β 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suY, Matrix.one_apply]

private theorem uX_mul_add (β : Kˣ) (c d : K) : uX β c * uX β d = uX β (c + d) := by
  apply Subtype.ext
  change blockSix (suX β c : Matrix (Fin 2) (Fin 2) K) *
      blockSix (suX β d : Matrix (Fin 2) (Fin 2) K) = blockSix (suX β (c + d) : Matrix _ _ K)
  rw [← blockSix_mul, ← Matrix.SpecialLinearGroup.coe_mul, suX_mul_add]

private theorem uY_mul_add (β : Kˣ) (c d : K) : uY β c * uY β d = uY β (c + d) := by
  apply Subtype.ext
  change blockSix (suY β c : Matrix (Fin 2) (Fin 2) K) *
      blockSix (suY β d : Matrix (Fin 2) (Fin 2) K) = blockSix (suY β (c + d) : Matrix _ _ K)
  rw [← blockSix_mul, ← Matrix.SpecialLinearGroup.coe_mul, suY_mul_add]

private theorem uX_zero (β : Kˣ) : uX β 0 = 1 := by
  apply Subtype.ext
  change blockSix (suX β 0 : Matrix (Fin 2) (Fin 2) K) = 1
  rw [suX_zero]
  exact blockSix_one (K := K)

private theorem uY_zero (β : Kˣ) : uY β 0 = 1 := by
  apply Subtype.ext
  change blockSix (suY β 0 : Matrix (Fin 2) (Fin 2) K) = 1
  rw [suY_zero]
  exact blockSix_one (K := K)

private theorem uX_pow (β : Kˣ) (c : K) (n : ℕ) : (uX β c) ^ n = uX β (n * c) := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, uX_zero, pow_zero]
  | succ n ih => rw [pow_succ, ih, uX_mul_add, Nat.cast_succ, add_mul, one_mul]

private theorem uY_pow (β : Kˣ) (c : K) (n : ℕ) : (uY β c) ^ n = uY β (n * c) := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, uY_zero, pow_zero]
  | succ n ih => rw [pow_succ, ih, uY_mul_add, Nat.cast_succ, add_mul, one_mul]

private theorem uX_pow_ringChar (β : Kˣ) (c : K) : (uX β c) ^ ringChar K = 1 := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  rw [uX_pow, CharP.cast_eq_zero K (ringChar K), zero_mul, uX_zero]

private theorem uY_pow_ringChar (β : Kˣ) (c : K) : (uY β c) ^ ringChar K = 1 := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  rw [uY_pow, CharP.cast_eq_zero K (ringChar K), zero_mul, uY_zero]

private def diag2 (t : Kˣ) : SL2 K :=
  ⟨Matrix.diagonal ![((t : K)), (((t⁻¹ : Kˣ) : K))], by
    rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_two, Units.val_inv_eq_inv_val]⟩

private def suA (β : Kˣ) (t : Kˣ) : K :=
  -((t : K) + (β : K) ^ 2) / (((t : K) + 1) * ((β : K) ^ 2 - 1))

private def suB (β : Kˣ) (t : Kˣ) : K :=
  (β : K) ^ 2 * ((t : K) ^ 2 - 1) / ((t : K) * ((β : K) ^ 2 - 1) ^ 2)

private def suC (β : Kˣ) (t : Kˣ) : K :=
  ((t : K) * (β : K) ^ 2 + 1) / (((t : K) + 1) * ((β : K) ^ 2 - 1))

private theorem suX_suY_product (β : Kˣ) (t : Kˣ) (ht : (t : K) + 1 ≠ 0) (hβ : (β : K) ^ 2 ≠ 1) :
    suX β (suA β t) * suY β (suB β t) * suX β (suC β t) = diag2 t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suX, suY, diag2, suA, suB, suC, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal] <;>
    field_simp [show (β : K) ≠ 0 from β.ne_zero, ht, hβ] <;> ring

private theorem dSix_eq_blockSix_diag2 (t : Kˣ) :
    ((dSix t : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = blockSix (diag2 t : Matrix _ _ K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dSix, diag2, blockSix, Matrix.diagonal]

private theorem uX_uY_product (β : Kˣ) (t : Kˣ) (ht : (t : K) + 1 ≠ 0) (hβ : (β : K) ^ 2 ≠ 1) :
    uX β (suA β t) * uY β (suB β t) * uX β (suC β t) = dSix t := by
  apply Subtype.ext
  change blockSix (suX β (suA β t) : Matrix _ _ K) *
      blockSix (suY β (suB β t) : Matrix _ _ K) * blockSix (suX β (suC β t) : Matrix _ _ K) =
    ((dSix t : SL(6, K)) : Matrix _ _ K)
  rw [← blockSix_mul, ← blockSix_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, suX_suY_product β t ht hβ, dSix_eq_blockSix_diag2]

private theorem sigma_suA (σ : K ≃+* K) (hσσ : ∀ c : K, σ (σ c) = c) {β : Kˣ} {t : Kˣ}
    (hβσ : σ (β : K) = -((β : K))⁻¹) (htσ : σ (t : K) = (t : K)⁻¹)
    (ht1 : (1 : K) + (t : K) ≠ 0) (hβ2 : (β : K) ^ 2 ≠ 1) :
    σ (suA β t) = -suA β t := by
  rw [suA]
  simp only [map_neg, map_div₀, map_add, map_sub, map_pow, map_mul, map_one, map_inv₀,
    hβσ, htσ, hσσ]
  have htinv1 : (t : K)⁻¹ + 1 ≠ 0 := by
    have h : (t : K)⁻¹ + 1 = (1 + (t : K)) / (t : K) := by
      field_simp [t.ne_zero]
    rw [h]
    exact div_ne_zero ht1 t.ne_zero
  have hβ2inv : ((β : K)⁻¹) ^ 2 - 1 ≠ 0 := by
    have h : ((β : K)⁻¹) ^ 2 - 1 = (1 - (β : K) ^ 2) / (β : K) ^ 2 := by
      field_simp [β.ne_zero]
    rw [h]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hβ2)) (pow_ne_zero 2 β.ne_zero)
  have ht1' : (t : K) + 1 ≠ 0 := by simpa [add_comm] using ht1
  have hβ2' : (1 : K) - (β : K) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ2)
  rw [← sub_eq_zero]
  field_simp [ht1, ht1', htinv1, hβ2, hβ2', hβ2inv, t.ne_zero, β.ne_zero,
    mul_inv_cancel₀ ht1, inv_mul_cancel₀ ht1]
  ring

private theorem sigma_suB (σ : K ≃+* K) (hσσ : ∀ c : K, σ (σ c) = c) {β : Kˣ} {t : Kˣ}
    (hβσ : σ (β : K) = -((β : K))⁻¹) (htσ : σ (t : K) = (t : K)⁻¹)
    (ht1 : (1 : K) + (t : K) ≠ 0) (hβ2 : (β : K) ^ 2 ≠ 1) :
    σ (suB β t) = -suB β t := by
  rw [suB]
  simp only [map_neg, map_mul, map_div₀, map_add, map_sub, map_pow, map_one, map_inv₀,
    hβσ, htσ, hσσ]
  have htinv1 : (t : K)⁻¹ + 1 ≠ 0 := by
    have h : (t : K)⁻¹ + 1 = (1 + (t : K)) / (t : K) := by
      field_simp [t.ne_zero]
    rw [h]
    exact div_ne_zero ht1 t.ne_zero
  have hβ2inv : ((β : K)⁻¹) ^ 2 - 1 ≠ 0 := by
    have h : ((β : K)⁻¹) ^ 2 - 1 = (1 - (β : K) ^ 2) / (β : K) ^ 2 := by
      field_simp [β.ne_zero]
    rw [h]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hβ2)) (pow_ne_zero 2 β.ne_zero)
  have ht1' : (t : K) + 1 ≠ 0 := by simpa [add_comm] using ht1
  have hβ2' : (1 : K) - (β : K) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ2)
  rw [← sub_eq_zero]
  field_simp [ht1, ht1', htinv1, hβ2, hβ2', hβ2inv, t.ne_zero, β.ne_zero,
    mul_inv_cancel₀ ht1, inv_mul_cancel₀ ht1]
  ring

private theorem sigma_suC (σ : K ≃+* K) (hσσ : ∀ c : K, σ (σ c) = c) {β : Kˣ} {t : Kˣ}
    (hβσ : σ (β : K) = -((β : K))⁻¹) (htσ : σ (t : K) = (t : K)⁻¹)
    (ht1 : (1 : K) + (t : K) ≠ 0) (hβ2 : (β : K) ^ 2 ≠ 1) :
    σ (suC β t) = -suC β t := by
  rw [suC]
  simp only [map_neg, map_add, map_mul, map_div₀, map_sub, map_pow, map_one, map_inv₀,
    hβσ, htσ, hσσ]
  have htinv1 : (t : K)⁻¹ + 1 ≠ 0 := by
    have h : (t : K)⁻¹ + 1 = (1 + (t : K)) / (t : K) := by
      field_simp [t.ne_zero]
    rw [h]
    exact div_ne_zero ht1 t.ne_zero
  have hβ2inv : ((β : K)⁻¹) ^ 2 - 1 ≠ 0 := by
    have h : ((β : K)⁻¹) ^ 2 - 1 = (1 - (β : K) ^ 2) / (β : K) ^ 2 := by
      field_simp [β.ne_zero]
    rw [h]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hβ2)) (pow_ne_zero 2 β.ne_zero)
  have ht1' : (t : K) + 1 ≠ 0 := by simpa [add_comm] using ht1
  have hβ2' : (1 : K) - (β : K) ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ2)
  rw [← sub_eq_zero]
  field_simp [ht1, ht1', htinv1, hβ2, hβ2', hβ2inv, t.ne_zero, β.ne_zero,
    mul_inv_cancel₀ ht1, inv_mul_cancel₀ ht1]
  ring

private theorem sigma_involutive (k K : Type) [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) : ∀ c : K, σ (σ c) = c := by
  intro c
  letI : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

private theorem isPerfect_unitarySL_card (k K : Type) [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) : Group.IsPerfect (unitarySL σ.toRingHom) := by
  obtain ⟨f, hf, hqcard, hp⟩ := card_eq_ringChar_pow k
  let p := ringChar k
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hKp : Nat.card K = p ^ (2 * f) := by
    change Nat.card K = (ringChar k) ^ (2 * f)
    rw [hK, hqcard, ← pow_mul]
    congr 1
    omega
  have hK' : Nat.card K = (p ^ f) ^ 2 := by
    change Nat.card K = ((ringChar k) ^ f) ^ 2
    rw [hKp, ← pow_mul]
    congr 1
    omega
  have hσ' : ∀ c : K, σ c = c ^ p ^ f := by
    intro c
    rw [hσ, hqcard]
  exact isPerfect_unitarySL_gen (K := K) (p := p) (f := f) hK' hσ'

private theorem exists_beta (k K : Type) [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ)
    (ht : (t : K) ^ (Nat.card k + 1) = 1) (ht2 : (t : K) ^ 2 ≠ 1) :
    ∃ β : Kˣ, σ (β : K) = -((β : K))⁻¹ ∧ (β : K) ^ 2 ≠ 1 := by
  classical
  have htσ : σ (t : K) = (t : K)⁻¹ := by
    rw [hσ]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [mul_comm, ← pow_succ]
    exact ht
  have hdeg : (Nat.card K - 1) / (Nat.card k - 1) = Nat.card k + 1 := by
    rw [hK]
    have hq1 : 0 < Nat.card k - 1 := by
      have : 1 < Nat.card k := Finite.one_lt_card
      omega
    have hfac : Nat.card k ^ 2 - 1 = (Nat.card k - 1) * (Nat.card k + 1) := by
      zify [Nat.one_le_pow 2 (Nat.card k) (by omega), (show 1 ≤ Nat.card k by omega)]
      ring
    rw [hfac, Nat.mul_div_cancel_left _ hq1]
  obtain ⟨β₀, hβ₀norm⟩ := FiniteField.norm_surjective k K (-1)
  have hβ₀pow : β₀ ^ (Nat.card k + 1) = -1 := by
    have h := FiniteField.algebraMap_norm_eq_pow (K := k) (K' := K) (x := β₀)
    rw [hdeg, hβ₀norm] at h
    rw [← h]
    simp
  have hβ₀0 : β₀ ≠ 0 := by
    intro h
    simp [h] at hβ₀pow
  have hβ₀σ : σ β₀ = -β₀⁻¹ := by
    have h2 : β₀ ^ Nat.card k * β₀ = -1 := by
      rw [← pow_succ]
      exact hβ₀pow
    have h3 : β₀ ^ Nat.card k * (-β₀) = 1 := by
      rw [mul_neg, h2, neg_neg]
    have h4 : -β₀ = (β₀ ^ Nat.card k)⁻¹ := eq_inv_of_mul_eq_one_right h3
    have h5 : β₀ ^ Nat.card k = (-β₀)⁻¹ := by
      rw [h4, inv_inv]
    rw [hσ β₀, h5, inv_neg]
  refine ⟨if h : β₀ ^ 2 = 1 then
      Units.mk0 (β₀ * (t : K)) (mul_ne_zero hβ₀0 t.ne_zero)
    else Units.mk0 β₀ hβ₀0, ?_, ?_⟩
  · by_cases h : β₀ ^ 2 = 1
    · simp only [h, dif_pos, Units.val_mk0]
      change σ (β₀ * (t : K)) = -((β₀ * (t : K)))⁻¹
      rw [map_mul, hβ₀σ, htσ]
      field_simp [hβ₀0, t.ne_zero]
    · simp only [h, dif_neg, not_false_eq_true, Units.val_mk0]
      exact hβ₀σ
  · intro hh
    by_cases h : β₀ ^ 2 = 1
    · simp only [h, dif_pos] at hh
      apply ht2
      have hmul : ((β₀ : K) * (t : K)) ^ 2 = 1 := hh
      rw [mul_pow] at hmul
      rwa [h, one_mul] at hmul
    · simp only [h, dif_neg, not_false_eq_true] at hh
      exact h hh

private theorem exists_psi_t (k K : Type) [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ)
    (ht : (t : K) ^ (Nat.card k + 1) = 1) (ht2 : (t : K) ^ 2 ≠ 1) :
    ∃ (ε : K) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K),
      ε ≠ 0 ∧ σ ε = -ε ∧ IsPsiTw σ.toRingHom ε Ψ := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf, hqcard, hp⟩ := card_eq_ringChar_pow k
  let p := ringChar k
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hKp : Nat.card K = p ^ (2 * f) := by
    change Nat.card K = (ringChar k) ^ (2 * f)
    rw [hK, hqcard, ← pow_mul]
    congr 1
    omega
  have hσσ : ∀ c : K, σ (σ c) = c := by
    intro c
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have htσ : σ (t : K) = (t : K)⁻¹ := by
    rw [hσ]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [mul_comm, ← pow_succ]
    exact ht
  let ε : K := (t : K) - (t : K)⁻¹
  have hε : σ ε = -ε := by
    dsimp [ε]
    rw [map_sub, htσ, map_inv₀, htσ, inv_inv]
    ring
  have hε0 : ε ≠ 0 := by
    intro h
    apply ht2
    have h' : (t : K) * ε = (t : K) ^ 2 - 1 := by
      dsimp [ε]
      field_simp [t.ne_zero]
    rw [h, mul_zero] at h'
    linear_combination -h'
  obtain ⟨Ψ, hΨ⟩ := exists_isPsiTw (K := K) (p := ringChar k) (f := 2 * f)
    σ.toRingHom hσσ (ε := ε) hε0 hε hp (by omega) hKp
  exact ⟨ε, Ψ, hε0, hε, hΨ⟩

private theorem map_dSix_eq_torusWord (k K : Type) [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ) (htσ : σ (t : K) = (t : K)⁻¹)
    (ε : K) (hε0 : ε ≠ 0) (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K)
    (hΨ : IsPsiTw σ.toRingHom ε Ψ) :
    Ψ (dSix t) = torusWord σ hσ hK t := by
  have hDWt := map_DW_eq_orbitN (K := K) σ.toRingHom Ψ hΨ t htσ
    (torusUnit σ hσ hK t) (torusUnit_coe σ hσ hK t)
  have hDW1 := map_DW_eq_orbitN (K := K) σ.toRingHom Ψ hΨ (1 : Kˣ) (by simp)
    (torusUnit σ hσ hK 1) (torusUnit_coe σ hσ hK 1)
  rw [torusUnit_one σ hσ hK] at hDW1
  have hDWt' : Ψ (DW (t : K) (t : K)⁻¹) =
      (orbitN TwistTag.E6 K σ.toRingHom aSixteen (torusUnit σ hσ hK t) :
        ModGL TwistTag.E6.tag K) := by
    simpa [htσ] using hDWt
  have hDW1' : Ψ (DW 1 1) =
      (orbitN TwistTag.E6 K σ.toRingHom aSixteen 1 : ModGL TwistTag.E6.tag K) := by
    simpa using hDW1
  have htorus := torusWord_eq_orbitH σ hσ hK t
  rw [dSix_eq_SL t, map_mul, map_inv, hDWt', hDW1', htorus, orbitH, Subgroup.coe_mul,
    Subgroup.coe_inv]

private theorem torusWord_mem_closure_uniCent_aux (k K : Type) [Field k] [Finite k]
    [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ)
    (ht2 : (t : K) ^ 2 ≠ 1) (htσ : σ (t : K) = (t : K)⁻¹)
    (ε : K) (hε : σ ε = -ε) (hε0 : ε ≠ 0)
    (β : Kˣ) (hβσ : σ (β : K) = -((β : K))⁻¹) (hβ2 : (β : K) ^ 2 ≠ 1)
    (Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K) (hΨ : IsPsiTw σ.toRingHom ε Ψ) :
    torusWord σ hσ hK t ∈ Subgroup.closure {x : twistedE6RootGroup K σ |
      Commute x (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
        ⟨f4Z k, f4Z_mem_adjointGroup⟩) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  classical
  have hσσ : ∀ c : K, σ (σ c) = c := sigma_involutive k K σ hσ hK
  have ht1 : (1 : K) + (t : K) ≠ 0 := by
    intro h
    apply ht2
    have ht_eq : (t : K) = -1 := by linear_combination h
    rw [ht_eq]
    norm_num
  have ht1' : (t : K) + 1 ≠ 0 := by simpa [add_comm] using ht1
  have hA : σ (suA β t) = -suA β t := sigma_suA σ hσσ hβσ htσ ht1 hβ2
  have hB : σ (suB β t) = -suB β t := sigma_suB σ hσσ hβσ htσ ht1 hβ2
  have hC : σ (suC β t) = -suC β t := sigma_suC σ hσσ hβσ htσ ht1 hβ2
  have hperf : Group.IsPerfect (unitarySL σ.toRingHom) :=
    isPerfect_unitarySL_card k K σ hσ hK
  have hle := map_unitarySL_le_graphFixedRootGroup (K := K) (σ := σ.toRingHom) (ε := ε)
    (Ψ := Ψ) hΨ (fun x => σ.surjective x) hperf
  have hzSix : Ψ (zSix ε) = ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) :=
    map_zSix k K σ hfix hK Ψ hΨ hε0
  let z' : twistedE6RootGroup K σ :=
    (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
      ⟨f4Z k, f4Z_mem_adjointGroup⟩)
  let x1 : twistedE6RootGroup K σ :=
    ⟨Ψ (uX β (suA β t)), hle ⟨uX β (suA β t),
      uX_mem_unitarySL β (suA β t) σ.toRingHom hσσ hβσ hA, rfl⟩⟩
  let x2 : twistedE6RootGroup K σ :=
    ⟨Ψ (uY β (suB β t)), hle ⟨uY β (suB β t),
      uY_mem_unitarySL β (suB β t) σ.toRingHom hσσ hβσ hB, rfl⟩⟩
  let x3 : twistedE6RootGroup K σ :=
    ⟨Ψ (uX β (suC β t)), hle ⟨uX β (suC β t),
      uX_mem_unitarySL β (suC β t) σ.toRingHom hσσ hβσ hC, rfl⟩⟩
  have hx1c : Commute x1 z' := by
    apply Subtype.ext
    change Commute (Ψ (uX β (suA β t))) (z' : ModGL TwistTag.E6.tag K)
    exact hzSix ▸ (show Commute (Ψ (uX β (suA β t))) (Ψ (zSix ε)) from
      (show Commute (uX β (suA β t)) (zSix ε) from
        uX_mul_zSix β (suA β t) ε hε0).map Ψ)
  have hx2c : Commute x2 z' := by
    apply Subtype.ext
    change Commute (Ψ (uY β (suB β t))) (z' : ModGL TwistTag.E6.tag K)
    exact hzSix ▸ (show Commute (Ψ (uY β (suB β t))) (Ψ (zSix ε)) from
      (show Commute (uY β (suB β t)) (zSix ε) from
        uY_mul_zSix β (suB β t) ε hε0).map Ψ)
  have hx3c : Commute x3 z' := by
    apply Subtype.ext
    change Commute (Ψ (uX β (suC β t))) (z' : ModGL TwistTag.E6.tag K)
    exact hzSix ▸ (show Commute (Ψ (uX β (suC β t))) (Ψ (zSix ε)) from
      (show Commute (uX β (suC β t)) (zSix ε) from
        uX_mul_zSix β (suC β t) ε hε0).map Ψ)
  have hx1u : ∃ n : ℕ, x1 ^ (ringChar K ^ n) = 1 := by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    change (Ψ (uX β (suA β t))) ^ ringChar K = 1
    rw [← map_pow, uX_pow_ringChar, map_one]
  have hx2u : ∃ n : ℕ, x2 ^ (ringChar K ^ n) = 1 := by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    change (Ψ (uY β (suB β t))) ^ ringChar K = 1
    rw [← map_pow, uY_pow_ringChar, map_one]
  have hx3u : ∃ n : ℕ, x3 ^ (ringChar K ^ n) = 1 := by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    change (Ψ (uX β (suC β t))) ^ ringChar K = 1
    rw [← map_pow, uX_pow_ringChar, map_one]
  have hprod : x1 * x2 * x3 = torusWord σ hσ hK t := by
    apply Subtype.ext
    change Ψ (uX β (suA β t)) * Ψ (uY β (suB β t)) * Ψ (uX β (suC β t)) =
      (torusWord σ hσ hK t : ModGL TwistTag.E6.tag K)
    rw [← map_mul, ← map_mul, uX_uY_product β t ht1' hβ2]
    exact map_dSix_eq_torusWord k K σ hσ hK t htσ ε hε0 Ψ hΨ
  have hx1 : x1 ∈ Subgroup.closure {x : twistedE6RootGroup K σ |
      Commute x (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
        ⟨f4Z k, f4Z_mem_adjointGroup⟩) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} :=
    Subgroup.subset_closure ⟨hx1c, hx1u⟩
  have hx2 : x2 ∈ Subgroup.closure {x : twistedE6RootGroup K σ |
      Commute x (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
        ⟨f4Z k, f4Z_mem_adjointGroup⟩) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} :=
    Subgroup.subset_closure ⟨hx2c, hx2u⟩
  have hx3 : x3 ∈ Subgroup.closure {x : twistedE6RootGroup K σ |
      Commute x (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
        ⟨f4Z k, f4Z_mem_adjointGroup⟩) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} :=
    Subgroup.subset_closure ⟨hx3c, hx3u⟩
  exact hprod ▸ mul_mem (mul_mem hx1 hx2) hx3

theorem torusWord_mem_closure_uniCent (k K : Type) [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2) (t : Kˣ)
    (ht : (t : K) ^ (Nat.card k + 1) = 1) (ht2 : (t : K) ^ 2 ≠ 1) :
    torusWord σ hσ hK t ∈ Subgroup.closure {x : twistedE6RootGroup K σ |
      Commute x (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom)
        ⟨f4Z k, f4Z_mem_adjointGroup⟩) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} := by
  classical
  obtain ⟨ε, Ψ, hε0, hε, hΨ⟩ := exists_psi_t k K σ hσ hK t ht ht2
  obtain ⟨β, hβσ, hβ2⟩ := exists_beta k K σ hσ hK t ht ht2
  have htσ : σ (t : K) = (t : K)⁻¹ := by
    rw [hσ]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [mul_comm, ← pow_succ]
    exact ht
  exact torusWord_mem_closure_uniCent_aux k K σ hσ hfix hK t ht2 htσ ε hε hε0 β hβσ hβ2 Ψ hΨ

theorem twistedZUniClosing_two (k K : Type) [Field k] [Finite k] [Field K] [Finite K]
    [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2) (hq : Nat.card k % 3 = 2) (h3 : 3 ≤ Nat.card k)
    (D₁ : LangLevi TwClass.f4Six.tag k TwClass.f4Six.w) (ω : D₁.Lˣ) (hω : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag k)
    (hz : baseChangeGL (algebraMap k D₁.L) (z : ModGL TwClass.f4Six.tag k) =
      D₁.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
        TwClass.f4Six.tag.rank) ω) * D₁.g⁻¹)
    (_hz1 : z ≠ 1) :
    Subgroup.closure
      ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range :
          Set (twistedE6RootGroup K σ)) ∪
        {x : twistedE6RootGroup K σ |
          Commute x (((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom) z) ∧
            ∃ n : ℕ, x ^ (ringChar K ^ n) = 1}) = ⊤ := by
  set ι : adjointGroup Tag.F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hι
  have hq5 : 5 ≤ Nat.card k := by omega
  obtain ⟨t, ht, ht4⟩ := exists_unit_pow_succ_eq_one K (Nat.card k) hK hq5
  obtain ⟨f, hf⟩ := twisted_z_conj_f4Z k hq D₁ ω hω z hz
  have ht2 : (t : K) ^ 2 ≠ 1 := by
    intro h
    apply ht4
    calc (t : K) ^ 4 = ((t : K) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h, one_pow]
  have hd' : torusWord σ hσ hK t ∈ Subgroup.closure {x : twistedE6RootGroup K σ |
      Commute x (ι ⟨f4Z k, f4Z_mem_adjointGroup⟩) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} :=
    torusWord_mem_closure_uniCent k K σ hσ hfix hK t ht ht2
  set H : Subgroup (twistedE6RootGroup K σ) := Subgroup.closure
    ((ι.range : Set (twistedE6RootGroup K σ)) ∪
      {x : twistedE6RootGroup K σ |
        Commute x (ι z) ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1}) with hH
  have hzι : ι z = ι f * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * (ι f)⁻¹ := by
    rw [← hf, map_mul, map_mul, map_inv]
  have hιf : ι f ∈ H := Subgroup.subset_closure (Or.inl ⟨f, rfl⟩)
  have hle : Subgroup.closure {x : twistedE6RootGroup K σ |
      Commute x (ι ⟨f4Z k, f4Z_mem_adjointGroup⟩) ∧
        ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} ≤ H := by
    rw [Subgroup.closure_le]
    rintro x ⟨hx, huni⟩
    have hcent : Commute (ι f * x * (ι f)⁻¹) (ι z) := by
      rw [Commute, hzι]
      calc (ι f * x * (ι f)⁻¹) * (ι f * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * (ι f)⁻¹)
          = ι f * (x * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩) * (ι f)⁻¹ := by group
        _ = ι f * (ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * x) * (ι f)⁻¹ := by rw [hx.eq]
        _ = (ι f * ι ⟨f4Z k, f4Z_mem_adjointGroup⟩ * (ι f)⁻¹) *
              (ι f * x * (ι f)⁻¹) := by group
    have huni' : ∃ n : ℕ, (ι f * x * (ι f)⁻¹) ^ (ringChar K ^ n) = 1 := by
      obtain ⟨n, hn⟩ := huni
      exact ⟨n, by
        rw [show ι f * x * (ι f)⁻¹ = (MulAut.conj (ι f)) x from rfl, ← map_pow, hn, map_one]⟩
    have hxH : ι f * x * (ι f)⁻¹ ∈ H := Subgroup.subset_closure (Or.inr ⟨hcent, huni'⟩)
    have hxeq : x = (ι f)⁻¹ * (ι f * x * (ι f)⁻¹) * ι f := by group
    rw [hxeq]
    exact mul_mem (mul_mem (inv_mem hιf) hxH) hιf
  have hF : (phiG σ hfix).range ≤ H := by
    rintro _ ⟨g, rfl⟩
    refine Subgroup.subset_closure (Or.inl ⟨e6FixedF4EquivAll k g, ?_⟩)
    simp [hι]
  have hd : torusWord σ hσ hK t ∈ H := hle hd'
  exact closure_top_of_torusWord σ hσ hfix hK H hF t ht ht4 hd

end CFSG.LieType.SeitzGeneration.ExcHighThree
