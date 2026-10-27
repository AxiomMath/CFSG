module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthCent
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlComp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronElts
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOPc
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecChar
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self reflGL rotGL)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem kron_signPair_mem {n : ℕ} {W₀ j : Matrix (Fin 2) (Fin 2) K} {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j) {i i' : Fin n}
    (hii' : i ≠ i') :
    signGL K (pairSet {i, i'}) ∈ (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  have h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1 := by ring
  have e : kronGL K n ⁅reflGL (K := K) i, rotGL i i' hii' h01⁆ = signGL K (pairSet {i, i'}) :=
    Units.ext (by rw [coe_kronGL, signMat_pair_eq_commutator hii' h01, kronI_signMat,
      coe_signGL])
  rw [← e, map_commutatorElement]
  exact commutator_mem_commutator (kronGL_mem_isoCent_blkDiag hR hA (reflGL_orth i))
    (kronGL_mem_isoCent_blkDiag hR hA (rotGL_orth hii' h01))

theorem kron_perm_mem {n : ℕ} {W₀ j : Matrix (Fin 2) (Fin 2) K} {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j)
    (σ τ : Equiv.Perm (Fin n)) :
    kronGL K n ⁅permGL K n σ, permGL K n τ⁆ ∈
      (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  rw [map_commutatorElement]
  exact commutator_mem_commutator (kronGL_mem_isoCent_blkDiag hR hA (permGL_orth σ))
    (kronGL_mem_isoCent_blkDiag hR hA (permGL_orth τ))

abbrev pi4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem commutator_perm4 :
    (⁅Equiv.swap (0 : Fin 4) 2 * Equiv.swap 1 3, Equiv.swap (0 : Fin 4) 1⁆)⁻¹ = pi4 := by
  decide

theorem pi4_permMatrix_sq : pi4.permMatrix K * pi4.permMatrix K = 1 := by
  rw [← Matrix.permMatrix_mul]
  have : pi4 * pi4 = 1 := by decide
  rw [this, Matrix.permMatrix_one]

theorem pi4_vals : pi4 0 = 1 ∧ pi4 1 = 0 ∧ pi4 2 = 3 ∧ pi4 3 = 2 := by decide

theorem pi4_permMatrix_apply (i j : Fin 4) :
    pi4.permMatrix K i j = if pi4 i = j then 1 else 0 := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, eq_comm]

theorem sign01_pi4 :
    signMat K {0, 1} * pi4.permMatrix K =
      pi4.permMatrix K * signMat K ({0, 1} : Finset (Fin 4)) := by
  ext i j
  simp only [signMat, diagonal_mul, mul_diagonal, pi4_permMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp +decide

theorem sign02_pi4 :
    signMat K {0, 2} * pi4.permMatrix K =
      -(pi4.permMatrix K * signMat K ({0, 2} : Finset (Fin 4))) := by
  ext i j
  simp only [signMat, diagonal_mul, mul_diagonal, pi4_permMatrix_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp +decide

theorem diag_pi4_zero (v : Fin 4 → K) : (diagonal v * pi4.permMatrix K) 0 0 = 0 := by
  rw [diagonal_mul, pi4_permMatrix_apply, pi4_vals.1]
  simp

theorem kronI_diag_pi4_ne (v : Fin 4 → K) (c : Kˣ) :
    kronI K 4 (diagonal v * pi4.permMatrix K) ≠
      ((GeneralLinearGroup.scalar (Fin (2 * 4)) c : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
  intro h
  have e := congrFun (congrFun h (pairEquiv 4 (0, 0))) (pairEquiv 4 (0, 0))
  rw [kronI_apply] at e
  simp only [↓reduceIte] at e
  rw [diag_pi4_zero, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at e
  exact c.ne_zero e.symm

theorem false_of_pc [Finite K] (hK : ringChar K ≠ 2) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hKc : Nat.card K = ℓ ^ f) {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 4 ≤ n)
    {R : GL (Fin (2 * n)) K}
    (hRm : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1)
    (hgA : (gs.val.left : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    {M : Subgroup (GL (Fin (2 * n)) K)} {Q : ℕ} (h : X10Data R gs M Q) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hRm, blkDiag_transpose, wMat, diagonal_transpose]
  have hN := C.isQuasisimple_isoCent_pc hK hℓ hKc hc (by omega) hRm hgA
  have hsign : ∀ i i' : Fin n, i ≠ i' → signGL K (pairSet {i, i'}) ∈
      (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * n)) K)) :=
    fun i i' hii' => kron_signPair_mem hRm hgA hii'
  rcases Nat.lt_or_ge 4 n with h5 | h4
  ·
    set i₀ : Fin n := ⟨0, by omega⟩
    set i₁ : Fin n := ⟨1, by omega⟩
    set i₂ : Fin n := ⟨2, by omega⟩
    set i₃ : Fin n := ⟨3, by omega⟩
    have hd : ∀ a b : Fin n, (a : ℕ) ≠ b → a ≠ b := fun a b hab h' => hab (by rw [h'])
    have h01 := hd i₀ i₁ (by simp [i₀, i₁])
    have h02 := hd i₀ i₂ (by simp [i₀, i₂])
    have h03 := hd i₀ i₃ (by simp [i₀, i₃])
    have h12 := hd i₁ i₂ (by simp [i₁, i₂])
    have h13 := hd i₁ i₃ (by simp [i₁, i₃])
    have h23 := hd i₂ i₃ (by simp [i₂, i₃])
    exact h.false_of_isoCent_e8 hK hRs hσ (Or.inr hN) (hsign _ _ h01) (hsign _ _ h02)
      (hsign _ _ h03) fun hX hY hZ => e8Triple_kron_sign h2 h5 h01 h02 h03 h12 h13 h23 hX hY hZ
  ·
    obtain rfl : n = 4 := by omega
    set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
    set τ : Equiv.Perm (Fin 4) := Equiv.swap 0 1
    set W := kronGL K 4 ⁅permGL K 4 σ, permGL K 4 τ⁆ with hWdef
    have hWm : (W : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (pi4.permMatrix K) := by
      rw [hWdef, coe_kronGL, coe_commutator_permGL, commutator_perm4]
    have hW := kron_perm_mem (K := K) hRm hgA σ τ
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    have h02 : (0 : Fin 4) ≠ 2 := by decide
    have h12 : (1 : Fin 4) ≠ 2 := by decide
    refine h.false_of_isoCent_e8 hK hRs hσ (Or.inr hN) (hsign _ _ h01) (hsign _ _ h02) hW
      fun hX hY hZ => ?_
    have hXm : ((signGL K (pairSet ({0, 1} : Finset (Fin 4))) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (signMat K {0, 1}) := by
      rw [coe_signGL, kronI_signMat]
    have hYm : ((signGL K (pairSet ({0, 2} : Finset (Fin 4))) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = kronI K 4 (signMat K {0, 2}) := by
      rw [coe_signGL, kronI_signMat]
    have hsq : ∀ T : Finset (Fin (2 * 4)), signGL K T * signGL K T = 1 := fun T =>
      Units.ext (by rw [Units.val_mul, coe_signGL, signMat_mul_self, Units.val_one])
    have hWW : W * W = 1 := Units.ext (by
      rw [Units.val_mul, hWm, ← map_mul, pi4_permMatrix_sq, map_one, Units.val_one])
    have hXW : signGL K (pairSet ({0, 1} : Finset (Fin 4))) * W =
        GeneralLinearGroup.scalar (Fin (2 * 4)) 1 * (W * signGL K (pairSet {0, 1})) := by
      rw [map_one, one_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hXm, hWm, ← map_mul, ← map_mul, sign01_pi4]
    have hYW : signGL K (pairSet ({0, 2} : Finset (Fin 4))) * W =
        GeneralLinearGroup.scalar (Fin (2 * 4)) (-1) * (W * signGL K (pairSet {0, 2})) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hYm, hWm, ← map_mul, ← map_mul,
        sign02_pi4, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_neg, Units.val_one,
        ← Matrix.smul_one_eq_diagonal, neg_one_smul, Matrix.neg_mul, Matrix.one_mul, map_neg]
    have hXY : signGL K (pairSet ({0, 1} : Finset (Fin 4))) * signGL K (pairSet {0, 2}) =
        GeneralLinearGroup.scalar (Fin (2 * 4)) 1 *
          (signGL K (pairSet {0, 2}) * signGL K (pairSet {0, 1})) := by
      rw [map_one, one_mul, signGL_mul_signGL, signGL_mul_signGL, symmDiff_comm]
    have hne_d : ∀ (v : Fin 4 → K) (Z : matrixDerived (oQ R)),
        ((Z : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
          kronI K 4 (diagonal v * pi4.permMatrix K) → projH _ Z ≠ 1 := fun v Z hZ =>
      projH_ne_one fun c' hc' => kronI_diag_pi4_ne v c' (by rw [← hZ, hc'])
    have hsgn : ∀ (T : Finset (Fin 4)) (Z : matrixDerived (oQ R)), T.Nonempty → Tᶜ.Nonempty →
        (Z : GL (Fin (2 * 4)) K) = signGL K (pairSet T) → projH _ Z ≠ 1 :=
      fun T Z h1 h1' hZ => projH_ne_one fun c' hc' => signGL_ne_scalar h2
        (pairSet_props ⟨h1, h1'⟩).1 (pairSet_props ⟨h1, h1'⟩).2 c' (hZ.symm.trans hc')
    have hone : GeneralLinearGroup.scalar (Fin (2 * 4)) (1 : Kˣ) = 1 := map_one _
    refine ⟨projH_sq_of_scalar 1 (by rw [hone]; exact hsq _),
      projH_sq_of_scalar 1 (by rw [hone]; exact hsq _),
      projH_sq_of_scalar 1 (by rw [hone]; exact hWW),
      projH_comm_of_scalar 1 hXY, projH_comm_of_scalar 1 hXW, projH_comm_of_scalar (-1) hYW,
      hsgn {0, 1} _ (by decide) ⟨2, by decide⟩ rfl, hsgn {0, 2} _ (by decide) ⟨1, by decide⟩ rfl,
      hne_d (fun _ => 1) _ (by rw [hWm, diagonal_one, Matrix.one_mul]), ?_, ?_, ?_, ?_⟩
    · rw [← map_mul]
      refine hsgn {1, 2} _ (by decide) ⟨0, by decide⟩ ?_
      change signGL K (pairSet {0, 1}) * signGL K (pairSet {0, 2}) = _
      rw [signGL_mul_signGL, ← pairSet_symmDiff, symmDiff_pair_pair h01 h02 h12]
    · rw [← map_mul]
      refine hne_d (fun i => if i ∈ ({0, 1} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 1}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, hXm, hWm, ← map_mul]
      rfl
    · rw [← map_mul]
      refine hne_d (fun i => if i ∈ ({0, 2} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 2}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, hYm, hWm, ← map_mul]
      rfl
    · rw [← map_mul, ← map_mul]
      refine hne_d ((fun i => if i ∈ ({0, 1} : Finset (Fin 4)) then -1 else 1) *
        fun i => if i ∈ ({0, 2} : Finset (Fin 4)) then -1 else 1) _ ?_
      change ((signGL K (pairSet {0, 1}) * signGL K (pairSet {0, 2}) * W : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = _
      rw [Units.val_mul, Units.val_mul, hXm, hYm, hWm, ← map_mul, ← map_mul, signMat, signMat,
        diagonal_mul_diagonal]
      rfl

end CFSG.ComponentClassification.GSThmB.X10Orth
