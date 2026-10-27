module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Data
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3
public import CFSG.HardMathSupport.Malle.SeitzCube.FrameBaseChange
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KGD.D4Frame

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.ExceptionalCover (cartanCoord)

open CFSG.RankThree.E6 (e6Index)


@[expose] def e6A2TorusChar {K : Type} [Field K] (i : Fin 3) (t : Fin 3 → Kˣ) :
    Fin Tag.E6.rank → Kˣ := fun k =>
  t 0 ^ (cartanCoord (τ := Tag.E6) (e6A2Simple₀ i) k + cartanCoord (τ := Tag.E6) (e6A2Simple₁ i) k) *
    t 1 ^ cartanCoord (τ := Tag.E6) (e6A2Simple₁ i) k


section Torus

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open CFSG.LieType.Chevalley (rootDiagUnit_mul)

open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

theorem e6A2_corootPair_eq : ∀ i : Fin 3, ∀ j : Fin 6,
    corootPair (τ := Tag.E6) (e6A2Simple₀ i) (Pi.single (e6Index j) 1) =
      cartanCoord (τ := Tag.E6) (e6A2Simple₀ i) (e6Index j) ∧
    corootPair (τ := Tag.E6) (e6A2Simple₁ i) (Pi.single (e6Index j) 1) =
      cartanCoord (τ := Tag.E6) (e6A2Simple₁ i) (e6Index j) := by
  decide +kernel

theorem e6A2_frame_pos (i : Fin 3) :
    e6A2Frame i ![1, 0] = e6A2Simple₀ i ∧ e6A2Frame i ![0, 1] = e6A2Simple₁ i ∧
      e6A2Frame i ![-1, 0] = -e6A2Simple₀ i ∧ e6A2Frame i ![0, -1] = -e6A2Simple₁ i := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext l <;> simp [e6A2Frame]

variable {K : Type} [Field K]

theorem conjSL_diagUnitOne_HSL (s u : Kˣ) :
    CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (HSL u) = HSL u := by
  apply Subtype.ext
  rw [CFSG.RankThree.Classical.coe_conjSL, CFSG.RankThree.Classical.coe_diagUnitOne,
    CFSG.RankThree.Classical.coe_diagUnitOne_inv]
  change !![(s : K), 0; 0, 1] * !![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)] *
    !![((s⁻¹ : Kˣ) : K), 0; 0, 1] = !![(u : K), 0; 0, ((u⁻¹ : Kˣ) : K)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

theorem sl3Hom_blockSL2_HSL_gen (i : Fin 3) (ψ : SL(3, K) →* ModGL Tag.E6 K) (c : Fin 2)
    (γp γn : Fin 2 → ℤ) (β : Fin Tag.E6.rank → ℤ) (hβ : IsRoot Tag.E6 β)
    (hp : γp ∈ RA2) (hn : γn ∈ RA2) (hFp : e6A2Frame i γp = β) (hFn : e6A2Frame i γn = -β)
    (hxp : ∀ t : K, CFSG.LieType.Steinberg.SL.x 2 K γp t =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne t)
    (hxn : ∀ t : K, CFSG.LieType.Steinberg.SL.x 2 K γn t =
      Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := c)).ne' t)
    (hψ : ∀ γ ∈ RA2, ∃ ε : Kˣ, ∀ c : K,
      ψ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = pinnedX Tag.E6 K (e6A2Frame i γ) ((ε : K) * c))
    (u : Kˣ) :
    ψ (blockSL2 K 2 c (HSL u)) = rootDiagUnit Tag.E6
      (fun k => u ^ corootPair (τ := Tag.E6) β (Pi.single k 1)) := by
  obtain ⟨a, ha⟩ := hψ γp hp
  obtain ⟨b, hb⟩ := hψ γn hn
  have hu : ∀ t : K, (ψ.comp (blockSL2 K 2 c)) (uSL t) = pinnedX Tag.E6 K β ((a : K) * t) := by
    intro t
    rw [MonoidHom.comp_apply, blockSL2_uSL_eq, ← hxp, ha, hFp]
  have hv : ∀ t : K, (ψ.comp (blockSL2 K 2 c)) (vSL t) = pinnedX Tag.E6 K (-β) ((b : K) * t) := by
    intro t
    rw [MonoidHom.comp_apply, blockSL2_vSL_eq, ← hxn, hb, hFn]
  obtain ⟨s, hs⟩ := exists_comp_conjSL_eq_rootSL2 hβ (ψ.comp (blockSL2 K 2 c)) a b hu hv
  calc ψ (blockSL2 K 2 c (HSL u)) = (ψ.comp (blockSL2 K 2 c)) (HSL u) := rfl
    _ = (ψ.comp (blockSL2 K 2 c))
          (CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s) (HSL u)) := by
        rw [conjSL_diagUnitOne_HSL]
    _ = rootSL2 Tag.E6 K β (HSL u) := by
        exact DFunLike.congr_fun hs (HSL u)
    _ = _ := rootSL2_HSL_eq hβ u

theorem isRoot_e6A2Simple₀ (i : Fin 3) : IsRoot Tag.E6 (e6A2Simple₀ i) := by
  have := isRoot_e6A2Root i (show (0 : Fin 3) ≠ 1 by decide)
  have h : e6A2Root i 0 1 = e6A2Simple₀ i := by simp [e6A2Root, e6A2Weight]
  rwa [h] at this

theorem isRoot_e6A2Simple₁ (i : Fin 3) : IsRoot Tag.E6 (e6A2Simple₁ i) := by
  have := isRoot_e6A2Root i (show (1 : Fin 3) ≠ 2 by decide)
  have h : e6A2Root i 1 2 = e6A2Simple₁ i := by simp [e6A2Root, e6A2Weight]
  rwa [h] at this

theorem sl3Hom_diag_eq_rootDiagUnit (i : Fin 3) (ψ : SL(3, K) →* ModGL Tag.E6 K)
    (hψ : ∀ γ ∈ RA2, ∃ ε : Kˣ, ∀ c : K,
      ψ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = pinnedX Tag.E6 K (e6A2Frame i γ) ((ε : K) * c))
    (t : Fin 3 → Kˣ) (A : SL(3, K))
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal fun j => (t j : K)) :
    ψ A = rootDiagUnit Tag.E6 (e6A2TorusChar i t) := by
  have hdet : (t 0 : K) * t 1 * t 2 = 1 := by
    have := A.2
    rw [hA, Matrix.det_diagonal, Fin.prod_univ_three] at this
    exact this
  have hAdec : A = blockSL2 K 2 0 (HSL (t 0)) * blockSL2 K 2 1 (HSL (t 0 * t 1)) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_HSL, coe_blockSL2_HSL, hA,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j
    · simp
    · simp
    · simp
      have h0 : (t 0 : K) ≠ 0 := (t 0).ne_zero
      have h1 : (t 1 : K) ≠ 0 := (t 1).ne_zero
      field_simp
      linear_combination hdet
  have hb0 := sl3Hom_blockSL2_HSL_gen i ψ 0 ![1, 0] ![-1, 0] (e6A2Simple₀ i)
    (isRoot_e6A2Simple₀ i)
    (mem_RA2_of_toStd (i := 0) (j := 1) (by decide) (by decide))
    (mem_RA2_of_toStd (i := 1) (j := 0) (by decide) (by decide))
    (e6A2_frame_pos i).1 (e6A2_frame_pos i).2.2.1
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t)
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t) hψ (t 0)
  have hb1 := sl3Hom_blockSL2_HSL_gen i ψ 1 ![0, 1] ![0, -1] (e6A2Simple₁ i)
    (isRoot_e6A2Simple₁ i)
    (mem_RA2_of_toStd (i := 1) (j := 2) (by decide) (by decide))
    (mem_RA2_of_toStd (i := 2) (j := 1) (by decide) (by decide))
    (e6A2_frame_pos i).2.1 (e6A2_frame_pos i).2.2.2
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t)
    (fun t => CFSG.LieType.Steinberg.SL.x_eq (by decide) (by decide) t) hψ (t 0 * t 1)
  rw [hAdec, map_mul, hb0, hb1, ← rootDiagUnit_mul]
  congr 1
  funext k
  have h := e6A2_corootPair_eq i k
  simp only [e6Index] at h
  obtain ⟨h0, h1⟩ := h
  simp only [Pi.mul_apply, e6A2TorusChar]
  rw [h0, h1, mul_zpow, zpow_add, mul_assoc]

theorem sl3Hom_diag_eq_rootDiagUnit_of_signs (i : Fin 3) (ψ : SL(3, K) →* ModGL Tag.E6 K)
    (s : (Fin 2 → ℤ) → ℤ) (hs : ∀ γ ∈ RA2, s γ = 1 ∨ s γ = -1)
    (hψ : ∀ γ ∈ RA2, ∀ c : K,
      ψ (CFSG.LieType.Steinberg.SL.x 2 K γ c) = pinnedX Tag.E6 K (e6A2Frame i γ) ((s γ : K) * c))
    (t : Fin 3 → Kˣ) (A : SL(3, K))
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal fun j => (t j : K)) :
    ψ A = rootDiagUnit Tag.E6 (e6A2TorusChar i t) := by
  refine sl3Hom_diag_eq_rootDiagUnit i ψ (fun γ hγ => ?_) t A hA
  have hss : (s γ : K) * (s γ : K) = 1 := by
    rcases hs γ hγ with h | h <;> rw [h] <;> simp
  exact ⟨Units.mkOfMulEqOne _ _ hss, hψ γ hγ⟩

end Torus

end CFSG.HardMathSupport.Malle.SeitzCube
