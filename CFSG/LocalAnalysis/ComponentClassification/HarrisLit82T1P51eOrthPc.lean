module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthSign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOPc
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairNorm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpModel
public import CFSG.LieType.Universal.Unitary.Clause0
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalGroups
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
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

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.CatLeafProof.X10Sp (CentralModel centralModel_SL
  CentralModel.of_mulEquiv CentralModel.of_centerQuotient_equiv)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.ComponentClassification.HarrisLit.T1.P51e.Comp (comp_map_mulEquiv)
open scoped MatrixGroups commutatorElement

theorem nonempty_centerQuotient_range {S G : Type*} [Group S] [Group G] (hS : IsQuasisimple S)
    (φ : S →* G) (hne : φ.range ≠ ⊥) : Nonempty (S ⧸ center S ≃* φ.range ⧸ center φ.range) := by
  have hker : φ.ker ≤ center S := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hS
      (Subgroup.Normal.isSubnormal (MonoidHom.normal_ker φ)) with h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
    · exact h
  exact LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hS φ.rangeRestrict
    φ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)

theorem centralModel_of_range {S G : Type} [Group S] [Group G] (hS : IsQuasisimple S)
    (φ : S →* G) {L : Subgroup G} (hL : φ.range = L) (hne : L ≠ ⊥) {ℓ : ℕ} {t : StatedLieTag}
    {n f : ℕ} (h : CentralModel ℓ t n f S) : CentralModel ℓ t n f L := by
  subst hL
  obtain ⟨e⟩ := nonempty_centerQuotient_range hS φ hne
  exact h.of_centerQuotient_equiv e.symm

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem one_le_of_card_eq [Finite K] {p f : ℕ} (hKc : Nat.card K = p ^ f) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with h0 | h
  · rw [h0, pow_zero] at hKc
    have := Finite.one_lt_card (α := K)
    omega
  · exact h

theorem centralModel_isoCent_unit (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c) {p f : ℕ}
    (hp : p.Prime) (hKc : Nat.card K = p ^ f) {n : ℕ} (hn : 3 ≤ n) {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) :
    CentralModel p .PSU n f (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  have : Fact (Irreducible (sqPoly c)) := ⟨irreducible_sqPoly hc⟩
  have h := unitaryFieldData_EAlg hc0 hp hKc
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (EAlg c) := h.finite
  have : CharP (EAlg c) p := h.charP
  have hσ : ∀ x : EAlg c, h.bar x = x ^ Nat.card K := fun x => by rw [h.bar_apply, hKc]
  have hW : ∀ x, ((phiE c).toRingHom x)ᵀ * wMat 1 (-c) =
      wMat 1 (-c) * (phiE c).toRingHom (h.bar x) := fun x => by
    rw [hσ]
    exact transpose_phiE_mul_wNeg hK hc x
  have hRG : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-c)) * resMat (phiE c).toRingHom n 1 := by
    rw [map_one, Matrix.mul_one, hR]
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiE c).toRingHom) (σ := h.bar)
    (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c) (wMat_inv_mul hc0) hW (phiE_root c)
    (fun M hM => phiE_mem_range hc0 hM) 1 hRG hA
  have hq : p ^ f ≠ 2 := by
    rw [← hKc]
    intro h2
    have := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
    rw [h2] at this
    exact (by decide : ¬ Odd 2) this
  have hF : Nat.card (EAlg c) = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hadm : StatedLieAdmissible .PSU n p f :=
    ⟨hp, one_le_of_card_eq hKc, hn, fun e => hq (Prod.ext_iff.1 e).2⟩
  have hSU : CentralModel p .PSU n f
      (LieType.Universal.Unitary.SU (LieType.BorelTits.unitaryInvolution (EAlg c) p f) n) :=
    ⟨hadm, Or.inl ⟨by decide,
      LieType.Universal.Unitary.statedClassicalModel_center_quotient hadm hF⟩⟩
  rw [hZ, commutator_uGrp_eq_unitarySU h hn hq]
  exact hSU.of_mulEquiv
    (((unitarySU p f (EAlg c) n).equivMapOfInjective _
      (resGL_injective (phiE_injective c) n)).symm.trans
      (LieType.Universal.Unitary.equivStatedSU hF n).symm)

omit [Finite K] in
theorem centralModel_isoCent_anti [Finite K] (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) {p f : ℕ}
    (hp : p.Prime) (hKc : Nat.card K = p ^ f) {n : ℕ} (hn : 3 ≤ n) {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(s ^ 2))))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat (s ^ 2))) :
    CentralModel p .PSL n f (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  have hc0 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hW₀ : wMat 1 (-(s ^ 2)⁻¹) * wMat 1 (-(s ^ 2)) = 1 := by
    rw [wMat, wMat, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hc0]
  have hRG : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-(s ^ 2))) * resMat (phiS h2 hs).toRingHom n 1 := by
    rw [map_one, Matrix.mul_one, hR]
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiS h2 hs).toRingHom) (σ := swapS)
    (r := (s, -s)) (phiS_injective h2 hs) hW₀ (fun x => transpose_phiS_mul h2 hs x)
    (phiS_root h2 hs) (fun M hM => phiS_mem_range h2 hs hM) 1 hRG hA
  have hadm : StatedLieAdmissible .PSL n p f :=
    ⟨hp, one_le_of_card_eq hKc, by omega, fun e => by have := (Prod.mk.inj e).1; omega,
      fun e => by have := (Prod.mk.inj e).1; omega⟩
  rw [hZ, commutator_uGrp_swap_eq hn]
  set ι := (iotaS n).comp (SpecialLinearGroup.toGL : SL(n, K) →* GL (Fin n) K) with hι
  have hinj : Function.Injective ι :=
    iotaS_injective.comp (fun x y h => Subtype.ext (congrArg Units.val h))
  exact (centralModel_SL hadm hKc).of_mulEquiv
    ((ι.range.equivMapOfInjective _ (resGL_injective (phiS_injective h2 hs) n)).symm.trans
      (MonoidHom.ofInjective hinj).symm)

theorem centralModel_isoCent_pc (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c)) :
    CentralModel p .PSL n f (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) ∨
      CentralModel p .PSU n f (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) := by
  by_cases hsq : IsSquare c
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hc (by rw [hs, mul_zero])
    have hcs : c = s ^ 2 := by rw [hs, sq]
    exact Or.inl (centralModel_isoCent_anti (Ring.two_ne_zero hK) hs0 hp hKc hn
      (by rw [hR, hcs]) (by rw [hA, hcs]))
  · exact Or.inr (centralModel_isoCent_unit hK hsq hp hKc hn hR hA)

theorem pc_comp_eq (hK : ringChar K ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (hKc : Nat.card K = ℓ ^ e)
    {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 3 ≤ n) {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {A : matrixDerived (oQ R)}
    (hA : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    {L : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hLH : L ≤ centralizer ({projH _ A} : Set _))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({projH _ A} : Set _)))) :
    ∃ hZΩ : (⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)) ≤ matrixDerived (oQ R),
      ((projH (matrixDerived (oQ R))).comp
        (((⁅isoCent R A, isoCent R A⁆ : Subgroup (GL (Fin (2 * n)) K)).subgroupOf
          (matrixDerived (oQ R))).subtype.comp (subgroupOfEquivOfLe hZΩ).symm.toMonoidHom)).range =
        L := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose, wMat, diagonal_transpose]
  set Z := isoCent R (A : GL (Fin (2 * n)) K) with hZ
  have hq := isQuasisimple_isoCent_pc hK hℓ hKc hc hn hR hA
  have hZΩ : ⁅Z, Z⁆ ≤ matrixDerived (oQ R) := by
    rw [matrixDerived_oQ h2 R hRs]
    exact commutator_mono inf_le_left inf_le_left
  set N := ((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R))).map (projH _) with hN
  have hleN : ∀ {M : Subgroup (StatedProj (matrixDerived (oQ R)))},
      M ≤ centralizer ({projH _ A} : Set _) → ⁅M, M⁆ = M → M ≤ N := by
    intro M hM hperf
    refine (le_map_commutator_of_perfect A hM hperf).trans (map_mono ?_)
    rw [commutator_le]
    intro B hB B' hB'
    rw [mem_subgroupOf]
    have hZB : ∀ {C : matrixDerived (oQ R)}, C ∈ centralizer ({A} : Set _) →
        (C : GL (Fin (2 * n)) K) ∈ Z := by
      intro C hC
      refine ⟨?_, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hC))⟩
      have := matrixDerived_le_isometries (oQ R) C.2
      rwa [matrixIsometries_oQ h2 R hRs] at this
    exact commutator_mem_commutator (hZB hB) (hZB hB')
  have hNC : N ≤ centralizer ({projH _ A} : Set _) := by
    rintro _ ⟨g, hg, rfl⟩
    replace hg : (g : GL (Fin (2 * n)) K) ∈ ⁅Z, Z⁆ := hg
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hgZ : (g : GL (Fin (2 * n)) K) ∈ Z := commutator_le_self _ hg
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 hgZ).2
  set φ := (projH (matrixDerived (oQ R))).comp
    (((⁅Z, Z⁆).subgroupOf (matrixDerived (oQ R))).subtype.comp
      (subgroupOfEquivOfLe hZΩ).symm.toMonoidHom) with hφ
  have hφr : φ.range = N := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (subgroupOfEquivOfLe hZΩ).symm.surjective, Subgroup.map_top, Subgroup.range_subtype]
  have hLN := hleN hLH (commutator_eq_of_isPComponent hLH hL)
  have hNq : IsQuasisimple N := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq φ with h | h
    · exfalso
      rw [hφr] at h
      rw [h, le_bot_iff] at hLN
      exact ne_bot_of_isPComponent hLH hL hLN
    · rwa [hφr] at h
  exact ⟨hZΩ, hφr.trans (eq_of_le_of_isQuasisimple hLN hNC hL hNq).symm⟩

theorem pc_comp_centralModel (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) {c : K} (hc : c ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    {R : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-c)))
    {A : matrixDerived (oQ R)}
    (hA : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat c))
    {L : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hLH : L ≤ centralizer ({projH _ A} : Set _))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({projH _ A} : Set _)))) :
    CentralModel p .PSL n f L ∨ CentralModel p .PSU n f L := by
  obtain ⟨hZΩ, hφ⟩ := pc_comp_eq hK hp hKc hc hn hR hA hLH hL
  have hq := isQuasisimple_isoCent_pc hK hp hKc hc hn hR hA
  have hne := ne_bot_of_isPComponent hLH hL
  rcases centralModel_isoCent_pc hK hp hKc hc hn hR hA with h | h
  · exact Or.inl (centralModel_of_range hq _ hφ hne h)
  · exact Or.inr (centralModel_of_range hq _ hφ hne h)

omit [Finite K] in
theorem even_of_skew' (h2 : (2 : K) ≠ 0) {d : ℕ} {R S : GL (Fin d) K}
    (hSR : (S : Matrix (Fin d) (Fin d) K)ᵀ * R = (-1 : K) • ((R : Matrix (Fin d) (Fin d) K) * S)) :
    Even d := by
  by_contra hodd
  have hodd' : Odd d := Nat.not_even_iff_odd.1 hodd
  have e := congrArg Matrix.det hSR
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin,
    hodd'.neg_one_pow] at e
  have hS := (Matrix.isUnits_det_units S).ne_zero
  have hR := (Matrix.isUnits_det_units R).ne_zero
  have : (2 : K) * ((S : Matrix (Fin d) (Fin d) K).det * (R : Matrix (Fin d) (Fin d) K).det) =
      0 := by linear_combination e
  rcases mul_eq_zero.1 this with h | h
  · exact h2 h
  · exact mul_ne_zero hS hR h

theorem pc_comp_centralModel_of_model (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = -1)
    {L : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hLH : L ≤ centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})
    (hL : IsPComponent 2 (L.subgroupOf (centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))}))) :
    ∃ n, d = 2 * n ∧ (CentralModel p .PSL n f L ∨ CentralModel p .PSU n f L) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  set Tm := (T : Matrix (Fin d) (Fin d) K) with hTm
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hiso : Tmᵀ * Rm * Tm = Rm := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  have hTT' : Tm * (-Tm) = 1 := by rw [Matrix.mul_neg, hT2, neg_neg]
  have hε : Tmᵀ * Rm = (-1 : K) • (Rm * Tm) := by
    calc Tmᵀ * Rm = Tmᵀ * Rm * (Tm * (-Tm)) := by rw [hTT', Matrix.mul_one]
      _ = Tmᵀ * Rm * Tm * (-Tm) := by rw [Matrix.mul_assoc (Tmᵀ * Rm)]
      _ = Rm * (-Tm) := by rw [hiso]
      _ = (-1 : K) • (Rm * Tm) := by rw [Matrix.mul_neg, neg_one_smul]
  have hS2 : Tm * Tm = (-1 : K) • 1 := by rw [neg_one_smul]; exact hT2
  have hc0 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨n, hn⟩ := even_of_skew' h2 hε
  obtain rfl : d = 2 * n := by omega
  refine ⟨n, rfl, ?_⟩
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc0 hS2 hε (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨hS, -, -⟩ := exists_transport_of_gram hgramR₁ (g := linPair T hTiso)
    (linPair_right T hTiso)
  set θ := oTransport H₁⁻¹ 1 hS with hθ
  set A := derivedTransport H₁⁻¹ 1 hS ⟨T, hT⟩ with hAdef
  have hAm : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat (-1 : K)) := by
    rw [hAdef, coe_derivedTransport, Units.val_mul, Units.val_mul, inv_inv]
    calc ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * Tm * H₁ =
        ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * (Tm * H₁) := by
          rw [Matrix.mul_assoc]
      _ = ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n (jMat (-1 : K))) := by
          rw [hAH₁]
      _ = blkDiag n (jMat (-1 : K)) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul]
  have hθz : θ (projH _ ⟨T, hT⟩) = projH _ A := by
    show oTransport H₁⁻¹ 1 hS (projH _ ⟨T, hT⟩) = projH _ (derivedTransport H₁⁻¹ 1 hS ⟨T, hT⟩)
    exact oTransport_proj _ _ _ _
  obtain ⟨hLH', hL'⟩ := comp_map_mulEquiv θ hLH hL
  rw [hθz] at hLH' hL'
  let eL : L ≃* L.map θ.toMonoidHom := L.equivMapOfInjective θ.toMonoidHom θ.injective
  rcases pc_comp_centralModel hK hp hKc hc0 (by omega) hR₁m hAm hLH' hL' with h | h
  · exact Or.inl (h.of_mulEquiv eL)
  · exact Or.inr (h.of_mulEquiv eL)

end CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth
