module

public import CFSG.HardMathSupport.C14IdxA2Hom
public import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUCore
public import CFSG.StronglyEmbedded.Catalog.Unitary
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.Timmesfeld.LieEmbed.SUTwistedE6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.SUnThreeLocal
open scoped MatrixGroups

private theorem oddDerivPair_facts
    {τ : Tag} {α β : Fin τ.rank → ℤ}
    (h : OddDerivPair τ α β) : IsRoot τ α ∧ IsRoot τ β ∧ α ≠ β := by
  have hB : oddDerivPairB τ α β = true := oddDerivPairB_iff.mpr h
  simp only [oddDerivPairB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hB
  refine ⟨RootOps.isRootB_iff.mp (by tauto), RootOps.isRootB_iff.mp (by tauto), ?_⟩
  have hne : CFSG.LieType.Ree.vecBEq α β = false := by tauto
  intro hab
  rw [hab, show CFSG.LieType.Ree.vecBEq β β = true from
    CFSG.LieType.Ree.vecBEq_iff.mpr rfl] at hne
  simp at hne

private theorem a2PairRoot_mem {τ : Tag} {α β : Fin τ.rank → ℤ} {i j : Fin 3}
    (hij : i ≠ j) : a2PairRoot α β i j ∈ a2PairRoots α β := by
  fin_cases i <;> fin_cases j <;> simp_all [a2PairRoot, a2PairRoots]

private theorem a2PairRoot_theta {τ : Tag} {α β : Fin τ.rank → ℤ}
    {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)} (hθα : θ α = β) (hθβ : θ β = α)
    (i j : Fin 3) :
    θ (a2PairRoot α β i j) = a2PairRoot α β (Fin.rev j) (Fin.rev i) := by
  fin_cases i <;> fin_cases j <;> simp [a2PairRoot, hθα, hθβ, add_comm]

private theorem typeAGraphConjugator_antidiag (K : Type) [Field K] [CharP K 2] :
    (↑(TauCeti.typeAGraphConjugator 2 K) : Matrix (Fin 3) (Fin 3) K) =
      CFSG.LieType.Universal.Unitary.antidiag 3 := by
  rw [CFSG.BenderSuzuki.Catalog.typeAGraphConjugator_eq_antidiag]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [CFSG.BenderSuzuki.Catalog.antidiag, CFSG.LieType.Universal.Unitary.antidiag]

private theorem unitarySteinberg_transvection (K : Type) [Field K] [CharP K 2]
    [ExpChar K 2] (e : ℕ) {i j : Fin 3} (hij : i ≠ j) (c : K) :
    CFSG.QuasithinUnique.SQTK.unitarySteinberg 2 2 e K
      (Matrix.SpecialLinearGroup.transvection hij c) =
    Matrix.SpecialLinearGroup.transvection (Fin.rev_injective.ne_iff.mpr hij).symm
      (c ^ 2 ^ e) := by
  unfold CFSG.QuasithinUnique.SQTK.unitarySteinberg
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hmap : Matrix.SpecialLinearGroup.map (iterateFrobenius K 2 e)
      (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij (c ^ 2 ^ e) := by
    ext a b
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
      iterateFrobenius_def]
  rw [hmap]
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [Matrix.SpecialLinearGroup.toGL_typeAGraphAutomorphism]
  set q := c ^ 2 ^ e
  rw [TauCeti.typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq]
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, typeAGraphConjugator_antidiag]
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    first
      | exfalso; exact hij rfl
      | simp_all [Matrix.SpecialLinearGroup.transvection_coe,
          Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply,
          CFSG.LieType.Universal.Unitary.antidiag, Fin.sum_univ_three,
          CharTwo.add_self_eq_zero]

private theorem rho_comp_block
    {τ : Tag} {L : Type} [Field L] [CharP L 2] {K : Type}
    [Field K] (ι : K →+* L) {α β : Fin τ.rank → ℤ} (hαβ : OddDerivPair τ α β)
    (ρ : SL(3, K) →* ModGL τ L)
    (hρ : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      ρ (Matrix.SpecialLinearGroup.transvection hij c) =
        pinnedX τ L (a2PairRoot α β i j) (ι c))
    (c : Fin 2) :
    ρ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 K 2 c) =
      (rootSL2 τ L (![α, β] c)).comp (Matrix.SpecialLinearGroup.map ι) := by
  have hidx1 : a2PairRoot α β c.castSucc c.succ = ![α, β] c := by
    fin_cases c <;> simp [a2PairRoot]
  have hidx2 : a2PairRoot α β c.succ c.castSucc = -![α, β] c := by
    fin_cases c <;> simp [a2PairRoot]
  have hroot : IsRoot τ (![α, β] c) := by
    fin_cases c
    · exact (oddDerivPair_facts hαβ).1
    · exact (oddDerivPair_facts hαβ).2.1
  refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
  rintro x (⟨t, rfl⟩ | ⟨t, rfl⟩)
  · change ρ (CFSG.ClassicalInvolution.WeakCT.blockSL2 K 2 c (uSL t)) =
      rootSL2 τ L (![α, β] c) (Matrix.SpecialLinearGroup.map ι (uSL t))
    have hs : (pinnedData τ (![α, β] c)).2.2 • ι t = ι t := by
      rcases pinnedSign_eq τ (![α, β] c) with h | h <;> simp [h, CharTwo.neg_eq]
    rw [CFSG.LieType.Chevalley.map_uSL, CFSG.HardMathSupport.Timmesfeld.CrossChar.blockSL2_uSL_eq,
      rootSL2_uSL_eq, hs]
    simpa [hidx1] using hρ c.castSucc c.succ (Fin.castSucc_lt_succ).ne t
  · change ρ (CFSG.ClassicalInvolution.WeakCT.blockSL2 K 2 c (vSL t)) =
      rootSL2 τ L (![α, β] c) (Matrix.SpecialLinearGroup.map ι (vSL t))
    obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := L) hroot
    have hε1 : ε = 1 := by
      have : (ε - 1) * (ε - 1) = 0 := by
        linear_combination hε + (1 - ε) * (CharTwo.two_eq_zero : (2 : L) = 0)
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    rw [CFSG.LieType.Chevalley.map_vSL, CFSG.HardMathSupport.Timmesfeld.CrossChar.blockSL2_vSL_eq,
      h, hε1, one_mul]
    simpa [hidx2] using hρ c.succ c.castSucc (Fin.castSucc_lt_succ).ne' t

private noncomputable abbrev suToSL (K : Type) [Field K] [Finite K] [CharP K 2] (e : ℕ) :
    SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3 →* SL(3, K) :=
  CFSG.Timmesfeld.LieEmbed.suToSL (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3

private theorem diagGL_mem_SU_a2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ℕ) (b : Kˣ) (hb : b ^ 2 ^ (2 * e) = b) :
    diagGL K 3 (fun a : Fin 3 => ![b, b⁻¹ * b ^ 2 ^ e, (b ^ 2 ^ e)⁻¹] a) ∈
      SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3 := by
  have hqq : 2 ^ e * 2 ^ e = 2 ^ (2 * e) := by
    rw [← pow_add]
    congr 1
    omega
  have hbq : (b ^ 2 ^ e) ^ 2 ^ e = b := by
    rw [← pow_mul, hqq]
    exact hb
  let d : Fin 3 → Kˣ := ![b, b⁻¹ * b ^ 2 ^ e, (b ^ 2 ^ e)⁻¹]
  change diagGL K 3 d ∈ SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3
  apply diagGL_mem_SU
  · intro a
    have h1u : d a ^ 2 ^ e * d (Fin.rev a) = 1 := by
      fin_cases a
      · change b ^ 2 ^ e * (b ^ 2 ^ e)⁻¹ = 1
        group
      · change (b⁻¹ * b ^ 2 ^ e) ^ 2 ^ e * (b⁻¹ * b ^ 2 ^ e) = 1
        rw [mul_pow, inv_pow, hbq]
        group
      · change ((b ^ 2 ^ e)⁻¹) ^ 2 ^ e * b = 1
        rw [inv_pow, hbq]
        group
    have := congrArg (fun u : Kˣ => (u : K)) h1u
    simpa [CFSG.LieType.BorelTits.unitaryInvolution_apply, iterateFrobenius_def,
      Units.val_mul, Units.val_pow_eq_pow_val] using this
  · rw [Fin.prod_univ_three]
    change b * (b⁻¹ * b ^ 2 ^ e) * (b ^ 2 ^ e)⁻¹ = 1
    group

private theorem suToSL_diag {K : Type} [Field K] [Finite K] [CharP K 2] (e : ℕ) (b : Kˣ)
    (hmem : diagGL K 3 (fun a : Fin 3 => ![b, b⁻¹ * b ^ 2 ^ e, (b ^ 2 ^ e)⁻¹] a) ∈
      SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3) :
    suToSL K e ⟨diagGL K 3 (fun a : Fin 3 => ![b, b⁻¹ * b ^ 2 ^ e, (b ^ 2 ^ e)⁻¹] a),
        hmem⟩ =
      CFSG.ClassicalInvolution.WeakCT.blockSL2 K 2 0 (HSL b) *
        CFSG.ClassicalInvolution.WeakCT.blockSL2 K 2 1 (HSL (b ^ 2 ^ e)) := by
  apply Subtype.ext
  change (((diagGL K 3 (fun a : Fin 3 => ![b, b⁻¹ * b ^ 2 ^ e, (b ^ 2 ^ e)⁻¹] a) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
    ((CFSG.ClassicalInvolution.WeakCT.blockSL2 K 2 0 (HSL b) *
      CFSG.ClassicalInvolution.WeakCT.blockSL2 K 2 1 (HSL (b ^ 2 ^ e)) : SL(3, K)) :
        Matrix (Fin 3) (Fin 3) K)
  rw [Matrix.SpecialLinearGroup.coe_mul,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.coe_blockSL2_HSL,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.coe_blockSL2_HSL,
    CFSG.ClassicalGroups.SUnThreeLocal.coe_diagGL, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

private theorem fixed_SU {K : Type} [Field K] [Finite K] [CharP K 2] (e : ℕ)
    (A : SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3) :
    CFSG.QuasithinUnique.SQTK.unitarySteinberg 2 2 e K (suToSL K e A) =
      suToSL K e A := by
  rw [← TauCeti.mem_fixedSubgroup]
  rw [CFSG.QuasithinUnique.SQTK.mem_fixedSubgroup_unitarySteinberg_iff]
  rw [typeAGraphConjugator_antidiag K]
  have hmem := (CFSG.LieType.Universal.Unitary.mem_SU.1 A.2).2
  have hmap : ((↑(suToSL K e A) : Matrix (Fin 3) (Fin 3) K)).map (fun x => x ^ 2 ^ e) =
      ((↑(suToSL K e A) : Matrix (Fin 3) (Fin 3) K)).map
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) := by
    congr 1
  rw [hmap]
  change ((((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map
      ⇑(iterateFrobenius K 2 e)).transpose *
    CFSG.LieType.Universal.Unitary.antidiag 3 *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        CFSG.LieType.Universal.Unitary.antidiag 3
  simpa [CFSG.LieType.Universal.Unitary.conjTr] using hmem

private theorem sigma_comp_rho (K : Type) [Field K] [CharP K 2] [ExpChar K 2] (e : ℕ)
    {τ : Tag} {L : Type} [Field L]
    {σ : ModGL τ L →* ModGL τ L} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    {α β : Fin τ.rank → ℤ} (hθα : θ α = β) (hθβ : θ β = α)
    (hσX : ∀ γ ∈ a2PairRoots α β, ∀ c : L,
      σ (pinnedX τ L γ c) = pinnedX τ L (θ γ) (c ^ 2 ^ e))
    (ι : K →+* L) (ρ : SL(3, K) →* ModGL τ L)
    (hρ : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      ρ (Matrix.SpecialLinearGroup.transvection hij c) =
        pinnedX τ L (a2PairRoot α β i j) (ι c)) :
    σ.comp ρ = ρ.comp (CFSG.QuasithinUnique.SQTK.unitarySteinberg 2 2 e K) := by
  refine MonoidHom.eq_of_eqOn_dense
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  simp only [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hρ i j hij c]
  rw [hσX (a2PairRoot α β i j) (a2PairRoot_mem hij) (ι c)]
  rw [a2PairRoot_theta hθα hθβ]
  rw [unitarySteinberg_transvection K e hij, hρ]
  rw [map_pow]

private theorem rho_mem_rootSpan
    {τ : Tag} {L : Type} [Field L] {K : Type} [Field K] {α β : Fin τ.rank → ℤ}
    (ι : K →+* L) (ρ : SL(3, K) →* ModGL τ L)
    (hρ : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K),
      ρ (Matrix.SpecialLinearGroup.transvection hij c) =
        pinnedX τ L (a2PairRoot α β i j) (ι c)) :
    ∀ g : SL(3, K), ρ g ∈ rootSpan τ L (a2PairRoots α β) := by
  intro g
  have hle : (⊤ : Subgroup (SL(3, K))) ≤ (rootSpan τ L (a2PairRoots α β)).comap ρ := by
    rw [← CFSG.ClassicalGroups.SpecialLinear.closure_transvection_eq_top (ι := Fin 3) (K := K),
      Subgroup.closure_le]
    rintro g ⟨i, j, hij, c, rfl⟩
    simpa [hρ i j hij c] using
      (pinnedX_mem_rootSpan (S := a2PairRoots α β) (a2PairRoot_mem hij) (ι c))
  exact hle (Subgroup.mem_top g)

private theorem map_SU_le_D
    {τ : Tag} {L : Type} [Field L]
    {K : Type} [Field K] [Finite K] [CharP K 2] (e : ℕ)
    (hF : Nat.card K = (2 ^ e) ^ 2) {σ : ModGL τ L →* ModGL τ L}
    {α β : Fin τ.rank → ℤ} (ρ : SL(3, K) →* ModGL τ L)
    (hcomp : σ.comp ρ = ρ.comp (CFSG.QuasithinUnique.SQTK.unitarySteinberg 2 2 e K))
    (hFrFix : ∀ A : SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3,
      CFSG.QuasithinUnique.SQTK.unitarySteinberg 2 2 e K (suToSL K e A) = suToSL K e A)
    (hroot : ∀ g : SL(3, K), ρ g ∈ rootSpan τ L (a2PairRoots α β))
    (A : SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3) :
    ρ (suToSL K e A) ∈ Subgroup.closure {x : ModGL τ L |
      x ∈ rootSpan τ L (a2PairRoots α β) ∧ σ x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  have hgen : (⊤ : Subgroup (SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3)) ≤
      Subgroup.closure {x : SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3 |
        ∃ j, x ^ 2 ^ j = 1} :=
    CFSG.StandardType.RootCentSU.top_le_closure_SU (F := K) (f := e) hF (by norm_num)
  have hpre : Subgroup.closure {x : SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3 |
        ∃ j, x ^ 2 ^ j = 1} ≤
      (Subgroup.closure {x : ModGL τ L |
        x ∈ rootSpan τ L (a2PairRoots α β) ∧ σ x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}).comap
        (ρ.comp (suToSL K e)) := by
    rw [Subgroup.closure_le]
    rintro x ⟨j, hx⟩
    refine Subgroup.subset_closure ⟨hroot (suToSL K e x), ?_, j, ?_⟩
    · change σ (ρ (suToSL K e x)) = ρ (suToSL K e x)
      calc σ (ρ (suToSL K e x)) =
          (ρ.comp (CFSG.QuasithinUnique.SQTK.unitarySteinberg 2 2 e K))
            (suToSL K e x) := by rw [← hcomp]; rfl
        _ = ρ (suToSL K e x) := by rw [MonoidHom.comp_apply, hFrFix x]
    · rw [← map_pow, hx, map_one]
  exact hpre (hgen (Subgroup.mem_top A))

private theorem rootDiagUnit_mul_tuples
    {τ : Tag} {L : Type} [Field L] {α β : Fin τ.rank → ℤ}
    (e : ℕ) (hαβ : OddDerivPair τ α β) (c : (Fin τ.rank → ℤ) → Lˣ)
    (hcβ : c β = c α ^ 2 ^ e) :
    rootDiagUnit τ (fun i => c α ^ corootPair α (Pi.single i 1)) *
      rootDiagUnit τ (fun i => (c α ^ 2 ^ e) ^ corootPair β (Pi.single i 1)) =
      rootDiagUnit τ (coordTuple {α, β} c) := by
  rw [← rootDiagUnit_mul]
  congr 1
  funext i
  rw [coordTuple, Finset.prod_pair (oddDerivPair_facts hαβ).2.2]
  simp only [Pi.mul_apply]
  rw [hcβ]

theorem rootDiagUnit_coordTuple_mem_closure_of_a2Pair
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e)
    {σ : ModGL τ L →* ModGL τ L} {θ : (Fin τ.rank → ℤ) ≃+ (Fin τ.rank → ℤ)}
    {α β : Fin τ.rank → ℤ} (hαβ : OddDerivPair τ α β) (hθα : θ α = β) (hθβ : θ β = α)
    (hσX : ∀ γ ∈ a2PairRoots α β, ∀ c : L,
      σ (pinnedX τ L γ c) = pinnedX τ L (θ γ) (c ^ 2 ^ e))
    (c : (Fin τ.rank → ℤ) → Lˣ) (hcβ : c β = c α ^ 2 ^ e) (hcα : c α = c β ^ 2 ^ e) :
    rootDiagUnit τ (coordTuple {α, β} c) ∈ Subgroup.closure {x : ModGL τ L |
      x ∈ rootSpan τ L (a2PairRoots α β) ∧ σ x = x ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} := by
  let K : Type := GaloisField 2 (2 * e)
  let ι : K →+* L := CFSG.BenderSuzuki.Catalog.galoisEmbedding 2 L (2 * e)
  have hF : Nat.card K = (2 ^ e) ^ 2 := by
    dsimp [K]
    rw [GaloisField.card 2 (2 * e) (by omega), show 2 * e = e * 2 by ring, pow_mul]
  have hbpow_u : c α ^ 2 ^ (2 * e) = c α := by
    rw [show 2 ^ (2 * e) = 2 ^ e * 2 ^ e by rw [← pow_add]; congr 1; omega, pow_mul,
      ← hcβ, hcα]
  have hbpow : (c α : L) ^ 2 ^ (2 * e) = (c α : L) := congrArg Units.val hbpow_u
  obtain ⟨b0, hb0⟩ := (CFSG.BenderSuzuki.Catalog.exists_galoisEmbedding_eq_iff
    (p := 2) (K := L) (k := 2 * e) (by omega) (c α)).mpr hbpow
  have hb0ne : b0 ≠ 0 := fun h => (c α).ne_zero (by rw [← hb0, h, map_zero])
  let bK : Kˣ := Units.mk0 b0 hb0ne
  have hbK : Units.map ι.toMonoidHom bK = c α := by
    apply Units.ext
    simpa [bK, ι] using hb0
  obtain ⟨ρ, hρ⟩ := exists_a2Hom_of_oddDerivPair (K := K) ι hαβ
  have hα := (oddDerivPair_facts hαβ).1
  have hβ := (oddDerivPair_facts hαβ).2.1
  have hbKpow : bK ^ 2 ^ (2 * e) = bK := by
    apply Units.ext
    apply ι.injective
    rw [Units.val_pow_eq_pow_val, map_pow,
      show ι (bK : K) = (c α : L) from congrArg Units.val hbK]
    exact hbpow
  have hcomp := sigma_comp_rho K e hθα hθβ hσX ι ρ hρ
  have hFrFix : ∀ A : SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3,
      CFSG.QuasithinUnique.SQTK.unitarySteinberg 2 2 e K (suToSL K e A) = suToSL K e A :=
    fun A => fixed_SU e A
  have hroot := rho_mem_rootSpan ι ρ hρ
  have hD := fun A => map_SU_le_D (τ := τ) (L := L) (K := K) e hF ρ hcomp hFrFix hroot A
  have hmem : diagGL K 3 (fun a : Fin 3 =>
      ![bK, bK⁻¹ * bK ^ 2 ^ e, (bK ^ 2 ^ e)⁻¹] a) ∈
        SU (CFSG.LieType.BorelTits.unitaryInvolution K 2 e) 3 :=
    diagGL_mem_SU_a2 e bK hbKpow
  have hdiag : ρ (suToSL K e ⟨diagGL K 3 (fun a : Fin 3 =>
      ![bK, bK⁻¹ * bK ^ 2 ^ e, (bK ^ 2 ^ e)⁻¹] a), hmem⟩) =
      rootDiagUnit τ (coordTuple {α, β} c) := by
    rw [suToSL_diag e bK hmem, map_mul]
    have h0 := congrArg (fun f : SL2 K →* ModGL τ L => f (HSL bK))
      (rho_comp_block (L := L) (K := K) ι hαβ ρ hρ (0 : Fin 2))
    have h1 := congrArg (fun f : SL2 K →* ModGL τ L => f (HSL (bK ^ 2 ^ e)))
      (rho_comp_block (L := L) (K := K) ι hαβ ρ hρ (1 : Fin 2))
    simp only [MonoidHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [h0, h1,
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.map_HSL_units,
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.map_HSL_units,
      map_pow, hbK, CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_HSL_eq hα,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_HSL_eq hβ]
    exact rootDiagUnit_mul_tuples e hαβ c hcβ
  rw [← hdiag]
  exact hD ⟨diagGL K 3 (fun a : Fin 3 =>
      ![bK, bK⁻¹ * bK ^ 2 ^ e, (bK ^ 2 ^ e)⁻¹] a), hmem⟩

end CFSG.HardMathSupport.C14Idx
