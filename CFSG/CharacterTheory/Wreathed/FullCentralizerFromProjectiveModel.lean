module

public import CFSG.CharacterTheory.Wreathed.ActualCentralizerSemilinear
public import CFSG.CharacterTheory.Wreathed.WreathedCentralCover
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
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

public noncomputable section
namespace CFSG.Wreathed.FullCentralizerFromProjectiveModel

universe u v
open Matrix
open CFSG.Wreathed.ActualProjectiveLayer
open CFSG.Wreathed.ActualCentralizerSemilinear
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Semidihedral.SemilinearOddExtensions
open CFSG.Semidihedral.OddFieldLift
open CFSG.Semidihedral.MatrixCover
open CFSG.Semidihedral.MatrixCoverData
open CFSG.Wreathed.WreathedCentralCover

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

theorem original_model_involution_mem
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    wreathModelHom (centralizerOddCoreSylow n hn S e)
        (centralizerOddCoreCoordinates n hn S e) (Original.x (2 ^ n)) ∈
      CFSG.layer (centralizerOddCoreQuotient n S e) := by
  rw [actual_quotient_involution_value n hn S e]
  exact centralizerActualLayer_involution_mem hnonab n hn S e hfour

theorem original_model_involution_eta
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F]
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (heta : eta (centralizerActualLayerInvolution hnonab n hn S e hfour) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    eta ⟨wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (Original.x (2 ^ n)),
        original_model_involution_mem hnonab n hn S e hfour⟩ =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  have hx : (⟨wreathModelHom (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (Original.x (2 ^ n)),
      original_model_involution_mem hnonab n hn S e hfour⟩ :
      CFSG.layer (centralizerOddCoreQuotient n S e)) =
    centralizerActualLayerInvolution hnonab n hn S e hfour :=
    Subtype.ext (actual_quotient_involution_value n hn S e)
  rw [hx]
  exact heta

omit [IsSimpleGroup G] in
theorem original_phi_kernel_central
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {F : Type v} [Field F] [Finite F]
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hlinear : LinearExtension F rho.range (actualField n hn S e rho)) :
    (actualPhi n hn S e rho hlinear).ker ≤
      Subgroup.center (centralizerOddCoreQuotient n S e) := by
  rw [actualPhi_ker n hn S e rho hrho hlinear,
    centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e]

theorem original_phi_layer_action
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
    (v : CFSG.layer (centralizerOddCoreQuotient n S e)) :
    slCoordinateAction F (eta v) = coordinateProjection F (actualField n hn S e rho)
      (actualPhi n hn S e rho hin.linear_extension) v := hin.action_values v

theorem actual_original_fixed_nonsquare_root
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
    (b : (FixedField F (actualField n hn S e rho))ˣ) (hb : ¬IsSquare b) :
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    ¬IsSquare (fixedUnit F (actualField n hn S e rho) b) ∧
      ∃ t : centralizerOddCoreQuotient n S e,
        t ∈ Subgroup.centralizer
          (CFSG.Wreathed.CentralTwoPowerFieldLift.E F (actualField n hn S e rho) phi hc :
            Set (centralizerOddCoreQuotient n S e)) ∧
        t ^ 2 = centralizerOddCoreMap n S e
          (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
            (Original.a (2 ^ n))) ∧
        t ^ (2 ^ n) = centralizerOddCoreMap n S e (centralInvolution n S e) ∧
        orderOf t = 2 * 2 ^ n ∧
        coordinateProjection F (actualField n hn S e rho) phi t =
          (jProjective F (fixedUnit F (actualField n hn S e rho) b) :
            Equiv.Perm (Omega F)) := by
  let phi := actualPhi n hn S e rho hin.linear_extension
  let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := hin.layer_normal
  have hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp, hp.odd_of_ne_two hpodd, hf, hcard⟩
  obtain ⟨hbF, t, ht, hsq, hpow, horder, hproj⟩ :=
    exists_original_fixed_j_square_root F hF (actualField n hn S e rho) hin.field_odd n hn
      (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e)
      phi (actualPhi_surjective n hn S e rho hin.linear_extension)
      (actualPhi_kernel_center_data n hn S e rho hrho hin.linear_extension).1 hc
      (CFSG.layer (centralizerOddCoreQuotient n S e)) hin.sylow_intersection eta
      (original_phi_layer_action hnonab n hn S e hfour p f theta rho eta hin) b hb
  refine ⟨hbF, t, ht, ?_, ?_, horder, hproj⟩
  · exact hsq.trans (actual_quotient_wreath_value n hn S e (Original.a (2 ^ n)))
  · exact hpow.trans (actual_quotient_involution_value n hn S e)

section OriginalFixedCentralizer

variable
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)

include hnonab n hn S e hfour p f theta rho hrho eta hin

local notation "H₀" => centralizerOddCoreQuotient n S e
local notation "M₀" => CFSG.layer H₀
local notation "Σ₀" => actualField n hn S e rho
local notation "φ₀" => actualPhi n hn S e rho hin.linear_extension
local notation "hc₀" => original_phi_kernel_central n hn S e rho hrho hin.linear_extension
local notation "E₀" => CFSG.Wreathed.CentralTwoPowerFieldLift.E F Σ₀ φ₀ hc₀

theorem actual_kernel_isPGroup
    : IsPGroup 2 (φ₀).ker :=
  CFSG.Wreathed.CentralTwoPowerFieldLift.kernel_isPGroup_of_card φ₀
    ⟨n, (actualPhi_kernel_center_data n hn S e rho hrho hin.linear_extension).2.2.2.2⟩

local notation "hK₀" => actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin
local notation "hsurj₀" => actualPhi_surjective n hn S e rho hin.linear_extension
local notation "e₀" => CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma F Σ₀ φ₀
  hsurj₀ hc₀ hK₀ hin.field_odd

theorem actual_eSigma_unique
    (sigma : Σ₀) :
    ∃! v : E₀, coordinateProjection F Σ₀ φ₀ v = fieldExtension F sigma := by
  refine ⟨e₀ sigma,
    CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective F Σ₀ φ₀
      hsurj₀ hc₀ hK₀ hin.field_odd sigma, ?_⟩
  intro v hv
  let eps := CFSG.Wreathed.CentralTwoPowerFieldLift.EEquivField F Σ₀ φ₀
    hsurj₀ hc₀ hK₀ hin.field_odd
  have he : coordinateProjection F Σ₀ φ₀ (e₀ (eps v)) = fieldExtension F (eps v) :=
    CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective F Σ₀ φ₀
      hsurj₀ hc₀ hK₀ hin.field_odd (eps v)
  have hev : e₀ (eps v) = v := eps.symm_apply_apply v
  rw [hev, hv] at he
  have hsig : eps v = sigma := by
    apply Subtype.ext
    apply RingEquiv.ext
    intro x
    have heval := congrArg (fun k : Equiv.Perm (Omega F) => k (some x)) he
    exact Option.some.inj heval.symm
  exact eps.injective (hsig.trans (eps.apply_symm_apply sigma).symm)

include hp hpodd hcard in
theorem actual_eSigma_entrywise
    (sigma : Σ₀) (v : M₀) :
    let : (M₀).Normal := hin.layer_normal
    eta (conjugateIn M₀ (e₀ sigma) v) =
      SpecialLinearGroup.map sigma.val.toRingHom (eta v) := by
  let : (M₀).Normal := hin.layer_normal
  let : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  exact compatible_conjugation_entrywise F p (hp.odd_of_ne_two hpodd) M₀ eta
    (coordinateProjection F Σ₀ φ₀)
    (original_phi_layer_action hnonab n hn S e hfour p f theta rho eta hin)
    (e₀ sigma) sigma
    (CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective F Σ₀ φ₀
      hsurj₀ hc₀ hK₀ hin.field_odd sigma) v

include hp hpodd hcard in
theorem actual_E_centralizer_mem_iff
    (v : M₀) :
    v ∈ (Subgroup.centralizer (E₀ : Set H₀)).subgroupOf M₀ ↔
      ∀ sigma : Σ₀, SpecialLinearGroup.map sigma.val.toRingHom (eta v) = eta v := by
  let : (M₀).Normal := hin.layer_normal
  constructor
  · intro hv sigma
    have hc : (e₀ sigma : H₀) * v = (v : H₀) * e₀ sigma :=
      Subgroup.mem_centralizer_iff.mp hv (e₀ sigma) (e₀ sigma).property
    have hfix : conjugateIn M₀ (e₀ sigma) v = v := by
      apply Subtype.ext
      rw [conjugateIn_coe, hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [← actual_eSigma_entrywise hnonab n hn S e hfour p f hp hpodd hcard
      theta rho hrho eta hin sigma v, hfix]
  · intro hv
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    let tE : E₀ := ⟨t, ht⟩
    let eps := CFSG.Wreathed.CentralTwoPowerFieldLift.EEquivField F Σ₀ φ₀
      hsurj₀ hc₀ hK₀ hin.field_odd
    let sigma := eps tE
    have heq : e₀ sigma = tE := eps.symm_apply_apply tE
    have h := actual_eSigma_entrywise hnonab n hn S e hfour p f hp hpodd hcard
      theta rho hrho eta hin sigma v
    rw [heq, hv sigma] at h
    have hfix : conjugateIn M₀ t v = v := eta.injective h
    have hh := congrArg (fun w : M₀ => (w : H₀)) hfix
    rw [conjugateIn_coe] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

include hp hpodd hcard in
theorem actual_eta_fixed_centralizer_image :
    ((Subgroup.centralizer (E₀ : Set H₀)).subgroupOf M₀).map eta.toMonoidHom =
      fixedEntrySL2 F Σ₀ := by
  ext X
  rw [mem_fixedEntrySL2]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (actual_E_centralizer_mem_iff hnonab n hn S e hfour p f hp hpodd hcard
      theta rho hrho eta hin v).mp hv
  · intro hX
    refine ⟨eta.symm X, ?_, eta.apply_symm_apply X⟩
    apply (actual_E_centralizer_mem_iff hnonab n hn S e hfour p f hp hpodd hcard
      theta rho hrho eta hin _).mpr
    rwa [eta.apply_symm_apply]

@[expose] def actualFixedCentralizerEquiv :
    (Subgroup.centralizer (E₀ : Set H₀)).subgroupOf M₀ ≃*
      SpecialLinearGroup (Fin 2) (FixedField F Σ₀) :=
  (eta.subgroupMap ((Subgroup.centralizer (E₀ : Set H₀)).subgroupOf M₀)).trans
    ((MulEquiv.subgroupCongr (actual_eta_fixed_centralizer_image hnonab n hn S e hfour
      p f hp hpodd hcard theta rho hrho eta hin)).trans (fixedSL2EquivRange F Σ₀).symm)

theorem actualFixedCentralizerEquiv_inclusion
    (v : (Subgroup.centralizer (E₀ : Set H₀)).subgroupOf M₀) :
    fixedSL2Inclusion F Σ₀
      (actualFixedCentralizerEquiv hnonab n hn S e hfour p f hp hpodd hcard
        theta rho hrho eta hin v) = eta v := by
  have h := (fixedSL2EquivRange F Σ₀).apply_symm_apply
    ((MulEquiv.subgroupCongr (actual_eta_fixed_centralizer_image hnonab n hn S e hfour
      p f hp hpodd hcard theta rho hrho eta hin))
      (eta.subgroupMap ((Subgroup.centralizer (E₀ : Set H₀)).subgroupOf M₀) v))
  exact congrArg Subtype.val h

end OriginalFixedCentralizer

structure ActualProjectiveCentralizerData
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F) : Prop where
  field_card : Nat.card F = p ^ f
  rho_injective : Function.Injective rho
  field_odd : Odd (Nat.card (actualField n hn S e rho))
  field_order_dvd : Nat.card (actualField n hn S e rho) ∣ f
  rho_layer : (centralizerSimpleLayer n hn S e).map rho = specialLayer F
  rho_range : rho.range = linearLayer F ⊔ liftedField F (actualField n hn S e rho)
  component : CFSG.IsComponent (CFSG.layer (centralizerOddCoreQuotient n S e))
  only_component : ∀ D : Subgroup (centralizerOddCoreQuotient n S e),
    CFSG.IsComponent D → D = CFSG.layer (centralizerOddCoreQuotient n S e)
  characteristic : (CFSG.layer (centralizerOddCoreQuotient n S e)).Characteristic
  full_center : centralizerFullCenterImage n hn S e =
    Subgroup.center (centralizerOddCoreQuotient n S e)
  full_centralizer : centralizerFullCenterImage n hn S e =
    Subgroup.centralizer (CFSG.layer (centralizerOddCoreQuotient n S e) :
      Set (centralizerOddCoreQuotient n S e))
  center_cyclic : IsCyclic (centralizerFullCenterImage n hn S e)
  center_card : Nat.card (centralizerFullCenterImage n hn S e) = 2 ^ n
  center_generator : centralizerFullCenterImage n hn S e = Subgroup.zpowers
    (centralizerOddCoreMap n S e
      (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
        (Original.a (2 ^ n))))
  layer_center : Subgroup.center (CFSG.layer (centralizerOddCoreQuotient n S e)) =
    (Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e))).subgroupOf
      (CFSG.layer (centralizerOddCoreQuotient n S e))
  involution : eta (centralizerActualLayerInvolution hnonab n hn S e hfour) =
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F
  projective : (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F).comp eta.toMonoidHom =
    theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour)
  action_values : ∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
    slCoordinateAction F (eta v) = (rho (centralizerFullQuotientMap n hn S e v)).val
  q_two_part : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n

theorem actual_projective_centralizer_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta) :
    ActualProjectiveCentralizerData hnonab n hn S e hfour p f theta rho eta := by
  have hM := actual_layer_component_data hnonab n hn S e hfour
  refine ⟨hcard, hrho, hin.field_odd, hin.field_order_dvd, hin.rho_layer,
    hin.linear_extension.1.2.2.1, hM.1, hM.2.1, hM.2.2.1,
    (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e).symm,
    hM.2.2.2.1.symm, inferInstance, centralizerFullCenterImage_card n hn S e,
    centralizerFullCenterImage_eq_zpowers n hn S e, hM.2.2.2.2,
    hin.involution, hin.projective, hin.action_values, hin.q_two_part⟩

theorem actual_projective_model_centralizer_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          SpecialLinearGroup (Fin 2) F),
        ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta ∧
        ActualProjectiveCentralizerData hnonab n hn S e hfour p f theta rho eta := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hrho, _, hin⟩ :=
    actual_projective_model_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  exact ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hin,
    actual_projective_centralizer_data hnonab n hn S e hfour p f hcard
      theta rho hrho eta hin⟩

open CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.Semidihedral.ProjectiveNonsquareInvolutions

structure ActualFullCentralizerData
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
    (hrho : Function.Injective rho) : Prop where
  structural : ActualProjectiveCentralizerData hnonab n hn S e hfour p f theta rho eta
  phi_values : ∀ v : centralizerOddCoreQuotient n S e,
    (actualPhi n hn S e rho hin.linear_extension v : coordinateE F) =
      rho (centralizerFullQuotientMap n hn S e v)
  fixed_field_card : Nat.card (FixedField F (actualField n hn S e rho)) =
    p ^ (f / Nat.card (actualField n hn S e rho))
  quotient_cyclic :
    let := hin.layer_normal
    IsCyclic (centralizerOddCoreQuotient n S e ⧸ CFSG.layer (centralizerOddCoreQuotient n S e))
  quotient_card :
    let := hin.layer_normal
    Nat.card (centralizerOddCoreQuotient n S e ⧸
      CFSG.layer (centralizerOddCoreQuotient n S e)) =
        2 ^ n * Nat.card (actualField n hn S e rho)
  group_card : Nat.card (centralizerOddCoreQuotient n S e) =
    2 ^ n * Nat.card (actualField n hn S e rho) * Nat.card F * (Nat.card F ^ 2 - 1)
  complement_membership :
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    ∀ t : centralizerOddCoreQuotient n S e,
      t ∈ CFSG.Wreathed.CentralTwoPowerFieldLift.E F (actualField n hn S e rho) phi hc ↔
        t ∈ B F (actualField n hn S e rho) phi ∧
          t ^ Nat.card (actualField n hn S e rho) = 1
  field_unique :
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    ∀ sigma : Sigma, ∃! t : CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma phi hc,
      coordinateProjection F Sigma phi t = fieldExtension F sigma
  field_entrywise :
    let := hin.layer_normal
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let hK := actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin
    ∀ sigma : Sigma, ∀ v : CFSG.layer (centralizerOddCoreQuotient n S e), ∀ i j : Fin 2,
      eta (conjugateIn (CFSG.layer (centralizerOddCoreQuotient n S e))
        (originalFieldLift F Sigma phi
          (actualPhi_surjective n hn S e rho hin.linear_extension) hc hK hin.field_odd sigma) v)
          i j = sigma.val (eta v i j)
  fixed_centralizer :
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F (actualField n hn S e rho) phi hc
    ((Subgroup.centralizer (E0 : Set (centralizerOddCoreQuotient n S e))).subgroupOf
      (CFSG.layer (centralizerOddCoreQuotient n S e))).map eta.toMonoidHom =
        (fixedSL2Inclusion F (actualField n hn S e rho)).range
  fixed_centralizer_equiv :
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma phi hc
    ∃ eps : (Subgroup.centralizer (E0 : Set (centralizerOddCoreQuotient n S e))).subgroupOf
      (CFSG.layer (centralizerOddCoreQuotient n S e)) ≃*
        SpecialLinearGroup (Fin 2) (FixedField F Sigma),
      ∀ v, fixedSL2Inclusion F Sigma (eps v) = eta v
  every_nonsquare : ∀ (b : (FixedField F (actualField n hn S e rho))ˣ), ¬IsSquare b →
    let Sigma := actualField n hn S e rho
    let phi := actualPhi n hn S e rho hin.linear_extension
    let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
    let E0 := CFSG.Wreathed.CentralTwoPowerFieldLift.E F Sigma phi hc
    let hK := actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin
    let eField := originalFieldLift F Sigma phi
      (actualPhi_surjective n hn S e rho hin.linear_extension) hc hK hin.field_odd
    let m := 2 ^ n
    let hm : 0 < m := by positivity
    let heven : Even m := even_two.pow_of_ne_zero (by omega)
    let hfix := original_fixed_parameter F Sigma b
    ¬IsSquare (fixedUnit F Sigma b) ∧
      ∃ tau : centralizerOddCoreQuotient n S e,
        tau ∈ Subgroup.centralizer (E0 : Set (centralizerOddCoreQuotient n S e)) ∧
        tau ^ 2 = centralizerOddCoreMap n S e
          (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
            (Original.a m)) ∧
        tau ^ m = centralizerOddCoreMap n S e (centralInvolution n S e) ∧
        orderOf tau = 2 * m ∧
        coordinateProjection F Sigma phi tau =
          (jProjective F (fixedUnit F Sigma b) : Equiv.Perm (Omega F)) ∧
        ∃ Phi : SemilinearExtension F (fixedUnit F Sigma b) m hm heven Sigma hfix ≃*
            centralizerOddCoreQuotient n S e,
          (∀ X j sigma, Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩ =
            (eta.symm X : centralizerOddCoreQuotient n S e) * tau ^ j.val * eField sigma) ∧
          (∀ X : SpecialLinearGroup (Fin 2) F,
            Phi ⟨specialInclusion F (fixedUnit F Sigma b) m hm heven X, 1⟩ =
              (eta.symm X : centralizerOddCoreQuotient n S e)) ∧
          Phi ⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ = tau ∧
          Phi (⟨cyclicGenerator F (fixedUnit F Sigma b) m hm heven, 1⟩ ^ 2) =
            centralizerOddCoreMap n S e
              (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
                (Original.a m)) ∧
          (∀ sigma : Sigma, Phi ⟨1, sigma⟩ = eField sigma) ∧
          (∀ sigma : Sigma, ∃! v : E0,
            coordinateProjection F Sigma phi v = fieldExtension F sigma ∧
              Phi ⟨1, sigma⟩ = (v : centralizerOddCoreQuotient n S e)) ∧
          (∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (sigma : Sigma),
            coordinateProjection F Sigma phi
              (Phi ⟨quotientClass F (fixedUnit F Sigma b) m hm heven X j, sigma⟩) =
                coordinatePGLAction F (ProjGenLinGroup.mk (SpecialLinearGroup.toGL X *
                  nonsquareMatrix F (fixedUnit F Sigma b) ^ j.val)) * fieldExtension F sigma) ∧
          (CFSG.Wreathed.CentralSL2Abelianization.matrixLayer F (fixedUnit F Sigma b) m hm heven
            Sigma hfix).map Phi.toMonoidHom = CFSG.layer (centralizerOddCoreQuotient n S e)


theorem actual_originalLayerX_eta
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta) :
    eta (originalLayerX n hn (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
      hin.sylow_intersection) = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  have hx : originalLayerX n hn (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e) (CFSG.layer (centralizerOddCoreQuotient n S e))
      hin.sylow_intersection = centralizerActualLayerInvolution hnonab n hn S e hfour :=
    Subtype.ext (actual_quotient_involution_value n hn S e)
  rw [hx]
  exact hin.involution


theorem actual_full_centralizer_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta) :
    ActualFullCentralizerData hnonab n hn S e hfour p f theta rho eta hin hrho := by
  let := hin.layer_normal
  let Sigma := actualField n hn S e rho
  let phi := actualPhi n hn S e rho hin.linear_extension
  let hc := original_phi_kernel_central n hn S e rho hrho hin.linear_extension
  have hker := (actualPhi_kernel_center_data n hn S e rho hrho hin.linear_extension).1
  have hminus := actual_originalLayerX_eta hnonab n hn S e hfour p f theta rho eta hin
  obtain ⟨_, hfixed, hEmem, hEunique, hmodels, hcardH, hcyclic, hcardQ, hentry,
    hcentral, hequiv⟩ :=
    wreathed_central_cover_exact_matrix_field_model_of_finite F p f hp
      (hp.odd_of_ne_two hpodd) hf hcard Sigma hin.field_odd n hn
      (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e)
      phi (actualPhi_surjective n hn S e rho hin.linear_extension) hker hc
      (CFSG.layer (centralizerOddCoreQuotient n S e)) hin.sylow_intersection eta
      (original_phi_layer_action hnonab n hn S e hfour p f theta rho eta hin) hminus
  refine ⟨actual_projective_centralizer_data hnonab n hn S e hfour p f hcard
      theta rho hrho eta hin, actualPhi_coe n hn S e rho hin.linear_extension,
    hfixed, hcyclic, hcardQ, hcardH, hEmem, hEunique, hentry, hcentral, hequiv, ?_⟩
  intro b hb
  obtain ⟨hbF, tau, hctau, hsq, hpow, horder, hproj, Phi, hformula,
    hspecial, hgen, hgensq, hfield, hprojPhi, hmatrix⟩ := hmodels b hb
  refine ⟨hbF, tau, hctau, ?_, ?_, horder, hproj, Phi,
    hformula, hspecial, hgen, ?_, hfield, ?_, hprojPhi, hmatrix⟩
  · exact hsq.trans (actual_quotient_wreath_value n hn S e (Original.a (2 ^ n)))
  · exact hpow.trans (actual_quotient_involution_value n hn S e)
  · exact hgensq.trans (actual_quotient_wreath_value n hn S e (Original.a (2 ^ n)))
  · intro sigma
    obtain ⟨v, hv, huniq⟩ := hEunique sigma
    refine ⟨v, ⟨hv, ?_⟩, ?_⟩
    · rw [hfield]
      have he := CFSG.Wreathed.CentralTwoPowerFieldLift.eSigma_projective F Sigma phi
        (actualPhi_surjective n hn S e rho hin.linear_extension) hc
        (actual_kernel_isPGroup hnonab n hn S e hfour p f theta rho hrho eta hin)
        hin.field_odd sigma
      have heq := huniq _ he
      exact congrArg Subtype.val heq
    · intro w hw
      exact huniq w hw.1

theorem actual_supplied_projective_model_full_centralizer
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F]
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (theta : centralizerSimpleLayer n hn S e ≃*
      ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrho : Function.Injective rho)
    (hextends : ∀ l : centralizerSimpleLayer n hn S e,
      (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val)
    (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
      SpecialLinearGroup (Fin 2) F)
    (hprojective : (CFSG.Semidihedral.ProjectiveSL2Cover.nativeQuotient F).comp eta.toMonoidHom =
      theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour))
    (hinvolution : eta (centralizerActualLayerInvolution hnonab n hn S e hfour) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    ∃ hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta,
      ActualFullCentralizerData hnonab n hn S e hfour p f theta rho eta hin hrho := by
  let hin := actual_central_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hcard
    theta rho hrho hextends eta hprojective hinvolution
  exact ⟨hin, actual_full_centralizer_data hnonab n hn S e hfour p f hp hpodd hf hcard
    theta rho hrho eta hin⟩

theorem actual_projective_model_determines_full_centralizer
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          SpecialLinearGroup (Fin 2) F)
        (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
        (hrho : Function.Injective rho),
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        ActualFullCentralizerData hnonab n hn S e hfour p f theta rho eta hin hrho := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hrho, hextends, hin⟩ :=
    actual_projective_model_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  exact ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hin, hrho,
    hextends, actual_full_centralizer_data hnonab n hn S e hfour p f hp hpodd hf hcard
      theta rho hrho eta hin⟩

theorem actual_projective_layer_model_determines_full_centralizer
    {G₀ : Type} [Group G₀] [Finite G₀] [IsSimpleGroup G₀]
    (hnonab : ∃ a b : G₀, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G₀) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          SpecialLinearGroup (Fin 2) F)
        (hin : ActualCentralCoverInputs hnonab n hn S e hfour p f theta rho eta)
        (hrho : Function.Injective rho),
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        ActualFullCentralizerData hnonab n hn S e hfour p f theta rho eta hin hrho := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hrho, hextends, hin⟩ :=
    actual_stated_projective_model_cover_inputs hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  exact ⟨F, hfield, hfinite, hcard, hchar, hq, theta, rho, eta, hin, hrho,
    hextends, actual_full_centralizer_data hnonab n hn S e hfour p f hp hpodd hf hcard
      theta rho hrho eta hin⟩

end CFSG.Wreathed.FullCentralizerFromProjectiveModel
