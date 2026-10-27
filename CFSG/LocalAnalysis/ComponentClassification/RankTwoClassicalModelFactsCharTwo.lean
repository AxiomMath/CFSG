module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoChar2C0Basic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Linear
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Symplectic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Unitary
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Orthogonal
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenUnitary
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SQT
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
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoChar2C0 (isCharacteristicP_centralizer_of_normal_pGroup_le
  isCharacteristicP_centralizer_of_two_radical isCharacteristicP_centralizer_of_mulEquiv)

section Linear

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL

theorem isCharacteristicP_centralizer_projectiveSL {f n : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n)
    {k : Type*} [Field k] (hk : Nat.card k = 2 ^ f) (t : projectiveSL n k)
    (ht : orderOf t = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({t} : Set (projectiveSL n k))) := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨s, rfl, hs⟩ := exists_sl_lift t htt
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  set U := flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs) with hUdef
  set Q := U.map (proj n k) with hQdef
  have hlift : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)),
      ∃ A : SpecialLinearGroup (Fin n) k, proj n k A = c ∧ A * s = s * A := by
    intro c hc
    obtain ⟨A, rfl⟩ := proj_surjective n k c
    exact ⟨A, rfl, commute_of_proj_commute hs (mem_centralizer_singleton_iff.mp hc)⟩
  have hQC : Q ≤ centralizer ({proj n k s} : Set (projectiveSL n k)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, commute_of_mem_flagKernel hs hu]
  have hQp : IsPGroup 2 Q := isPGroup_flagKernel.map (proj n k)
  have hnorm : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)), ∀ q ∈ Q,
      c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨A, rfl, hAs⟩ := hlift c hc
    obtain ⟨u, hu, rfl⟩ := hq
    exact ⟨A * u * A⁻¹, conj_mem_flagKernel hs hAs hu, by rw [map_mul, map_mul, map_inv]⟩
  refine isCharacteristicP_centralizer_of_normal_pGroup_le hQC hQp hnorm (fun c hc hcQ => ?_)
  obtain ⟨A, rfl, hAs⟩ := hlift c hc
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    exact ⟨A, mem_flagKernel_of_commute_two hs hs1 hAs, rfl⟩
  · exact mem_map_flagKernel_of_commute hn3 hf hk (dispRange_ne_bot hs1)
      (dispRange_le_dispKer hs) (dispKer_ne_top hs1) fun u hu => hcQ _ ⟨u, hu, rfl⟩

theorem isCharacteristicP_centralizer_of_psl_model {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSL n 2 f) (u : X) (hu : orderOf u = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({u} : Set X)) := by
  obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  let e' : X ≃* LinearFlag.projectiveSL n K :=
    eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
  exact isCharacteristicP_centralizer_of_mulEquiv e'
    (isCharacteristicP_centralizer_projectiveSL hf hn hK) u hu

end Linear

section Symplectic

open Matrix CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem isCharacteristicP_centralizer_statedSp {f r : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r)
    {k : Type} [Field k] (hk : Nat.card k = 2 ^ f) (t : StatedProj (StatedSp r k))
    (ht : orderOf t = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({t} : Set (StatedProj (StatedSp r k)))) := by
  classical
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : NeZero r := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := UnitaryHigher.proj_bijective_of_charTwo (r := r) (K := k)
  have hιinj := spInner_injective (r := r) (K := k)
  obtain ⟨s, rfl⟩ := hbij.2 t
  have hsord : orderOf s = 2 := by rw [← orderOf_injective _ hbij.1 s, ht]
  have hs : s * s = 1 := by rw [← sq, ← hsord, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hsord
    exact absurd hsord (by norm_num)
  set W := displacement s with hWdef
  set L := (pairedSympForm k r).orthogonal W with hLdef
  set R := flagKernel W L with hRdef
  have hW0 : W ≠ ⊥ := by
    intro hbot
    refine hs1 (statedSp_ext fun v => ?_)
    have h1 : spMat s *ᵥ v - v ∈ W := mem_displacement.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
    rw [h1]
    exact (one_mulVec v).symm
  obtain ⟨-, hRp, hnorm, hcentEq, -⟩ :=
    even_symplectic_isotropic_radical_centralizer hr hf hk W hW0
      (isTotallyIsotropic_displacement hs)
  set Q := R.map (proj r k) with hQdef
  have hlift : ∀ c ∈ centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))),
      ∃ g : StatedSp r k, proj r k g = c ∧ g * s = s * g := by
    intro c hc
    obtain ⟨g, rfl⟩ := hbij.2 c
    refine ⟨g, rfl, hbij.1 ?_⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.mp hc
  have hQC : Q ≤ centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, commute_of_mem_flagKernel hs hh]
  have hQp : IsPGroup 2 Q := hRp.map (proj r k)
  have hconjR : ∀ g : StatedSp r k, g * s = s * g → ∀ h ∈ R, g * h * g⁻¹ ∈ R := by
    intro g hgs h hh
    have hgW : ∀ w ∈ W, ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
        *ᵥ (fun i => (1 : k ≃+* k) (w i)) ∈ W := by
      intro w hw
      obtain ⟨v, rfl⟩ := mem_displacement.mp hw
      refine mem_displacement.mpr ⟨spMat g *ᵥ v, ?_⟩
      change spMat s *ᵥ (spMat g *ᵥ v) - spMat g *ᵥ v = spMat g *ᵥ (spMat s *ᵥ v - v)
      rw [mulVec_sub, ← spMat_mul_mulVec, ← spMat_mul_mulVec, hgs]
    have hgn := hnorm g 1 hgW
    rw [map_one, mul_one] at hgn
    have hmem : spInner r k g * spInner r k h * (spInner r k g)⁻¹ ∈ R.map (spInner r k) :=
      (mem_normalizer_iff.mp hgn _).mp ⟨h, hh, rfl⟩
    obtain ⟨h', hh', hh'eq⟩ := hmem
    rw [← map_inv, ← map_mul, ← map_mul] at hh'eq
    rw [← hιinj hh'eq]
    exact hh'
  have hnormQ : ∀ c ∈ centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))),
      ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨g, rfl, hgs⟩ := hlift c hc
    obtain ⟨h, hh, rfl⟩ := hq
    exact ⟨g * h * g⁻¹, hconjR g hgs h hh, by rw [map_mul, map_mul, map_inv]⟩
  refine isCharacteristicP_centralizer_of_normal_pGroup_le hQC hQp hnormQ (fun c hc hcQ => ?_)
  obtain ⟨g, rfl, -⟩ := hlift c hc
  have hgR : ∀ h ∈ R, g * h = h * g := by
    intro h hh
    exact hbij.1 (by rw [map_mul, map_mul]; exact hcQ _ ⟨h, hh, rfl⟩)
  have hmem : spInner r k g ∈ spSemilinearAutGroup r k ⊓ centralizer
      ((R.map (spInner r k) : Subgroup (MulAut (StatedProj (StatedSp r k)))) : Set _) := by
    refine mem_inf.mpr ⟨spInner_mem_spSemilinearAutGroup g, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hgR h hh]
  rw [hcentEq] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  have hzg : (z : StatedSp r k) = g := hιinj hz
  exact ⟨z, hzg ▸ z.2, by rw [hzg]⟩

theorem isCharacteristicP_centralizer_of_psp_model {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSp n 2 f) (u : X) (hu : orderOf u = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({u} : Set X)) := by
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  exact isCharacteristicP_centralizer_of_mulEquiv eT
    (isCharacteristicP_centralizer_statedSp hf (by omega) hK) u hu

end Symplectic

section Unitary

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.ComponentClassification.UnbalancingLocal.EvenUnitaryComponents
open CFSG.ClassicalInvolution (exists_two_radical_primeFormConj)

theorem isCharacteristicP_centralizer_unitaryPSU {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (t : unitaryPSU h n) (ht : orderOf t = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({t} : Set (unitaryPSU h n))) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv h hC
  have hconj := conj_injective_primeFormP h hC hn
  have : Finite K := h.finite
  refine isCharacteristicP_centralizer_of_mulEquiv e.symm (fun t ht => ?_) t ht
  have hα2 : orderOf (MulAut.conj t) = 2 := by
    rw [orderOf_injective _ hconj]
    exact ht
  have hαinn : MulAut.conj t ∈ inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    ⟨t, rfl⟩
  have hF : primeFormFieldFactor h hC hn hq (MulAut.conj t) = RingEquiv.refl K := by
    have hαD : MulAut.conj t ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ (MulAut.conj t)).mp hαinn
      exact ⟨_, hs.symm⟩
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker] at hαD
    exact hαD
  obtain ⟨s, hs1, hss, hαs⟩ :=
    (even_unitary_involution_matrix_lifts h hC hn hq (MulAut.conj t) hα2).2.1 hF
  obtain ⟨R, hRX, hnorm, hR, hcent⟩ := exists_two_radical_primeFormConj h hC hn hq le_rfl s hs1 hss
  rw [← hαs] at hRX hnorm hcent
  exact isCharacteristicP_centralizer_of_two_radical (MulAut.conj : _ →* _) hconj R hRX hnorm hR
    hcent

theorem isCharacteristicP_centralizer_of_psu_model {X : Type} [Group X] {n f : ℕ}
    (hT : StatedClassicalModel X .PSU n 2 f) (u : X) (hu : orderOf u = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({u} : Set X)) := by
  obtain ⟨⟨-, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬ (n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  exact isCharacteristicP_centralizer_of_mulEquiv (eT.trans (unitaryPSUEquiv h (by omega)).symm)
    (isCharacteristicP_centralizer_unitaryPSU h hn hq') u hu

end Unitary

section Orthogonal

open QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
open CFSG.ClassicalInvolution (exists_two_radical_of_two_le_rank)

variable {K : Type} [Field K] {d : ℕ} [Finite K] [CharP K 2] {Q : QuadraticForm K (Fin d → K)}

theorem isCharacteristicP_centralizer_matrixProjectiveDerived (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (x : matrixProjectiveDerived Q) (hx : orderOf x = 2) :
    CFSG.IsCharacteristicP 2 (centralizer ({x} : Set (matrixProjectiveDerived Q))) := by
  have : Finite (matrixProjectiveDerived Q) := by
    have : Finite (GL (Fin d) K) := inferInstance
    infer_instance
  have hconj := conj_injective_matrixProjectiveDerived hQ hT hE
  obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q x
  have hα : MulAut.conj (matrixProjectiveProjection Q g) =
      matrixProjectiveConjugationHom Q
        (matrixIsometryInclusion Q (Subgroup.inclusion (matrixDerived_le_isometries Q) g)) :=
    (matrixProjectiveConjugationHom_derived Q g).symm
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hx
    omega
  have hg2 : g * g = 1 := by
    apply derivedKappa_injective hQ hT hE
    rw [map_mul, map_one, derivedKappa, MonoidHom.comp_apply,
      matrixProjectiveConjugationHom_derived, ← map_mul, ← pow_two, ← hx, pow_orderOf_eq_one,
      map_one]
  have hrank := two_le_rank_of_mem_derived hQ hT hE g hg1 hg2
  obtain ⟨R, hRX, hnorm, hR, hcent⟩ := exists_two_radical_of_two_le_rank hQ hT hE
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)) le_rfl
    (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := matrixProjectiveProjection_surjective Q y
      exact ⟨_, matrixProjectiveConjugationHom_derived Q h⟩)
    (Subgroup.inclusion (matrixDerived_le_isometries Q) g)
    (by rw [← hα, orderOf_injective _ hconj]; exact hx) hrank
  rw [← hα] at hRX hnorm hcent
  exact isCharacteristicP_centralizer_of_two_radical
    (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)) hconj R hRX
    hnorm hR hcent

omit [Finite K] [CharP K 2] in
theorem isCharacteristicP_centralizer_of_pOmega_model {T : Type} [Group T] {t : StatedLieTag}
    {n f : ℕ} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (hT : StatedClassicalModel T t n 2 f)
    (u : T) (hu : orderOf u = 2) : CFSG.IsCharacteristicP 2 (centralizer ({u} : Set T)) := by
  obtain ⟨-, hf, hn⟩ := hT.1
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadPlus n K (by omega)
    have hcomm := commutator_coordinateQuadPlus n K (by omega)
    exact isCharacteristicP_centralizer_of_mulEquiv (coordinatePlusWitnessEquiv K eT)
      (isCharacteristicP_centralizer_matrixProjectiveDerived hreg.1 hreg.2 hcomm) u hu
  · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨eT⟩⟩ := hT
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hf hK
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    have hcomm := commutator_coordinateQuadMinus n K b c hn hirr
    exact isCharacteristicP_centralizer_of_mulEquiv
      (coordinateMinusWitnessEquiv K (by omega) b c eT)
      (isCharacteristicP_centralizer_matrixProjectiveDerived hreg.1 hreg.2 hcomm) u hu

end Orthogonal

theorem classicalCentralizerCharTwo : ClassicalCentralizerCharTwo := by
  intro X _ _ hT u hu
  obtain ⟨hfam, -, -⟩ := hT
  rcases hfam with ⟨n, m, -, h⟩ | ⟨n, m, -, h⟩ | ⟨n, m, -, h⟩ | ⟨n, m, -, h | h⟩
  · exact isCharacteristicP_centralizer_of_psl_model h u hu
  · exact isCharacteristicP_centralizer_of_psu_model h u hu
  · exact isCharacteristicP_centralizer_of_psp_model h u hu
  · exact isCharacteristicP_centralizer_of_pOmega_model (Or.inl rfl) h u hu
  · exact isCharacteristicP_centralizer_of_pOmega_model (Or.inr rfl) h u hu

end CFSG.ComponentClassification.RankTwoClassical
