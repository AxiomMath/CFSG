module

public import CFSG.LieType.SeitzGeneration.UnitaryTwoNonCubeCore
public import CFSG.LieType.SeitzGeneration.UnitaryTwoNonCubeToral
public import CFSG.LieType.SeitzGeneration.InnerThreeUnitaryLeaves
public import CFSG.LieType.SeitzGeneration.OuterUnitaryWide
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyClosed
public import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzFineU5
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem cube_eq_one_of_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) {μ : K} (hμ : μ ≠ 0) :
    μ ^ 3 = 1 := by
  have hfin := h.finite
  have := Fintype.ofFinite K
  have hcard : Nat.card K = 4 := by
    rw [h.card_eq_sq, hq]
    norm_num
  have h1 := FiniteField.pow_card_sub_one_eq_one μ hμ
  rwa [← Nat.card_eq_fintype_card, hcard] at h1

theorem scalar_ne_zero_of_cube (hn : 0 < n) {x : GL (Fin n) K} {α : K}
    (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1) : α ≠ 0 := by
  rintro rfl
  have h1 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((((x ^ 3)⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hx3, zero_smul, Matrix.zero_mul] at h1
  have := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simp at this

theorem closure_planeFixUn_abelian_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (hn : 5 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ primeFormUnitary h (idGram K n))
    (hy : y ∈ primeFormUnitary h (idGram K n)) (hxy : x * y = y * x) {α β : K} (hα : α ≠ 0)
    (hβ : β ≠ 0) (hx3 : ((x ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = α • 1)
    (hy3 : ((y ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = β • 1)
    (hind : ∀ a b : ℕ,
      (∃ c : K, ((x ^ a * y ^ b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) →
        3 ∣ a ∧ 3 ∣ b) :
    Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
      FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ⊤ := by
  classical
  have hfin := h.finite
  have hn1 : 1 ≤ n := by omega
  have hnx : ∀ c : K, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 := fun c hc => by
    have := hind 1 0 ⟨c, by simpa using hc⟩
    omega
  have hny : ∀ c : K, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 := fun c hc => by
    have := hind 0 1 ⟨c, by simpa using hc⟩
    omega
  have hnxy : ∀ c : K, ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 :=
    fun c hc => by
      have := hind 1 1 ⟨c, by simpa using hc⟩
      omega
  have hnxy2 : ∀ c : K, ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ c • 1 :=
    fun c hc => by
      have := hind 1 2 ⟨c, by simpa using hc⟩
      omega
  have hxyU : x * y ∈ primeFormUnitary h (idGram K n) := mul_mem hx hy
  have hxy2U : x * y ^ 2 ∈ primeFormUnitary h (idGram K n) := mul_mem hx (pow_mem hy 2)
  have hxy3 : ((x * y) ^ 3 : GL (Fin n) K) = x ^ 3 * y ^ 3 := by
    rw [(Commute.mul_pow (show Commute x y from hxy) 3)]
  have hxy23 : ((x * y ^ 2) ^ 3 : GL (Fin n) K) = x ^ 3 * (y ^ 3) ^ 2 := by
    rw [Commute.mul_pow (show Commute x (y ^ 2) from (show Commute x y from hxy).pow_right 2) 3,
      ← pow_mul, ← pow_mul, mul_comm 2 3]
  have hcom : ∀ a b : GL (Fin n) K, (((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (a : Matrix (Fin n) (Fin n) K) * (b : Matrix (Fin n) (Fin n) K) := fun a b => rfl
  have hc1 : (((x * y) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (α * β) • 1 := by
    rw [hxy3, hcom, hx3, hy3, smul_mul_smul_comm, mul_one]
  have hc2 : (((x * y ^ 2) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (α * β ^ 2) • 1 := by
    rw [hxy23, hcom, hx3, Units.val_pow_eq_pow_val, hy3, _root_.smul_pow, one_pow,
      smul_mul_smul_comm, mul_one]
  have hfull : ∀ S : Set (unitarySU ℓ f K n),
      S ⊆ (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →
      Subgroup.closure S = ⊤ →
      Subgroup.closure (FixUn ℓ f n K (x : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K (y : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∪
        FixUn ℓ f n K ((x * y ^ 2 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = ⊤ :=
    fun S hS hT => top_unique (by rw [← hT]; exact Subgroup.closure_mono hS)
  by_cases hcx : ∃ μ : K, μ ^ 3 = α
  · by_cases hcy : ∃ ν : K, ν ^ 3 = β
    ·
      obtain ⟨μ, hμ⟩ := hcx
      obtain ⟨ν, hν⟩ := hcy
      have hα1 : α = 1 := by
        rw [← hμ]
        exact cube_eq_one_of_two h hq (fun h0 => hα (by rw [← hμ, h0]; norm_num))
      have hβ1 : β = 1 := by
        rw [← hν]
        exact cube_eq_one_of_two h hq (fun h0 => hβ (by rw [← hν, h0]; norm_num))
      refine closure_planeFixUn_toral_two h hq hn hx hy hxy ?_ ?_
      · apply Units.ext
        rw [hx3, hα1, one_smul, Units.val_one]
      · apply Units.ext
        rw [hy3, hβ1, one_smul, Units.val_one]
    ·
      refine hfull _ ?_ (closure_planeFixUn_abelian_noncube_two h hq hy hx hxy.symm hα hy3
        hx3 hnx hcy hcx hn1)
      intro g hg
      simp only [Set.mem_union] at hg ⊢
      tauto
  · by_cases hcy : ∃ ν : K, ν ^ 3 = β
    ·
      refine hfull _ ?_ (closure_planeFixUn_abelian_noncube_two h hq hx hy hxy hβ hx3 hy3
        hny hcx hcy hn1)
      intro g hg
      simp only [Set.mem_union] at hg ⊢
      tauto
    · rcases NonCube.cube_dichotomy hα hβ hcx hcy with hρ | hρ
      ·
        refine hfull _ ?_ (closure_planeFixUn_abelian_noncube_two h hq hx hxyU
          ((Commute.refl x).mul_right (show Commute x y from hxy)).eq (mul_ne_zero hα hβ) hx3
          hc1 hnxy hcx hρ hn1)
        intro g hg
        simp only [Set.mem_union] at hg ⊢
        tauto
      ·
        refine hfull _ ?_ (closure_planeFixUn_abelian_noncube_two h hq hx hxy2U
          ((Commute.refl x).mul_right ((show Commute x y from hxy).pow_right 2)).eq
          (mul_ne_zero hα (pow_ne_zero 2 hβ)) hx3 hc2 hnxy2 hcx hρ hn1)
        intro g hg
        simp only [Set.mem_union] at hg ⊢
        tauto

theorem unitaryTwoOrderNinePlanes_holds : UnitaryTwoOrderNinePlanes := by
  intro ℓ f n K _ h hq hn x y hx hy hxy α β hx3 hy3 _ hind
  have hsu : ∀ g : GL (Fin n) K, g ∈ unitarySU ℓ f K n → g ∈ primeFormUnitary h (idGram K n) :=
    fun g hg => ((le_of_eq (unitarySU_eq_gramSU h n)) hg).1
  exact closure_planeFixUn_abelian_two h hq hn (hsu x hx) (hsu y hy) hxy
    (scalar_ne_zero_of_cube (by omega) hx3) (scalar_ne_zero_of_cube (by omega) hy3) hx3 hy3 hind

theorem planeGen_of_diag_abelian_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
    (hn5 : 5 ≤ n) {E : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2) (hD : E ≤ primeFormD h (idGram K n))
    (hab : DiagLiftsCommute h E) : PlaneGen E := by
  classical
  have hn : 3 ≤ n := by omega
  have hfin := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : 0 < n := by omega
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair Nat.prime_three E hE.2 hc
  set κ := primeFormConjHom h (idGram K n) with hκ
  obtain ⟨A₁, hA₁⟩ : ∃ A : primeFormUnitary h (idGram K n), κ A = e₁ := hD he₁
  obtain ⟨A₂, hA₂⟩ : ∃ A : primeFormUnitary h (idGram K n), κ A = e₂ := hD he₂
  have hA₁E : κ A₁ ∈ E := hA₁ ▸ he₁
  have hA₂E : κ A₂ ∈ E := hA₂ ▸ he₂
  have hcomm : A₁ * A₂ = A₂ * A₁ := hab A₁ A₂ hA₁E hA₂E
  have hcube : ∀ A : primeFormUnitary h (idGram K n), κ A ∈ E →
      ∃ α : Kˣ, ((A : GL (Fin n) K) ^ 3 : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) α := by
    intro A hA
    have h1 : κ (A ^ 3) = 1 := by rw [map_pow]; exact hE.2 _ hA
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn (A ^ 3)).1 h1
    exact ⟨c, hc'⟩
  obtain ⟨α, hα⟩ := hcube A₁ hA₁E
  obtain ⟨β, hβ⟩ := hcube A₂ hA₂E
  have hx3 : (((A₁ : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (α : K) • 1 := by rw [hα]; exact coe_scalarGL α
  have hy3 : (((A₂ : GL (Fin n) K) ^ 3 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (β : K) • 1 := by rw [hβ]; exact coe_scalarGL β
  have hind : ∀ a b : ℕ, (∃ c : K, (((A₁ : GL (Fin n) K) ^ a * (A₂ : GL (Fin n) K) ^ b :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1) → 3 ∣ a ∧ 3 ∣ b := by
    rintro a b ⟨c, hcab⟩
    obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq hn0 hcab
    have hmem : (A₁ : GL (Fin n) K) ^ a * (A₂ : GL (Fin n) K) ^ b ∈
        primeFormUnitary h (idGram K n) := mul_mem (pow_mem A₁.2 a) (pow_mem A₂.2 b)
    have hnorm : h.norm (u : K) = 1 :=
      norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 (hu ▸ hmem)
    have h1 : κ (A₁ ^ a * A₂ ^ b) = 1 := by
      refine (OuterUnitaryWide.conjHom_eq_one_iff h hn _).2 ⟨u, hnorm, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
      exact hu
    rw [map_mul, map_pow, map_pow, hA₁, hA₂] at h1
    exact three_dvd_of_pow_mul_pow_eq_one (hE.2 _ he₁) (hE.2 _ he₂) he₂1 he₁₂ h1
  have hgen := closure_planeFixUn_abelian_two h hq hn5 A₁.2 A₂.2 (congrArg Subtype.val hcomm)
    α.ne_zero β.ne_zero hx3 hy3 hind
  have hne : ∀ k : ℕ, e₁ * e₂ ^ k ≠ 1 := by
    intro k hk
    apply he₁₂
    have : e₁ = (e₂ ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k)
  have hne1 : e₁ ≠ 1 := fun h1 => he₁₂ (h1 ▸ Subgroup.one_mem _)
  have hB3E : κ (A₁ * A₂) ∈ E := by rw [map_mul]; exact E.mul_mem hA₁E hA₂E
  have hB4E : κ (A₁ * A₂ ^ 2) ∈ E := by
    rw [map_mul, map_pow]; exact E.mul_mem hA₁E (E.pow_mem hA₂E 2)
  refine OuterUnitaryWide.planeGen_of_closure_fixUn h hn ?_
  rw [eq_top_iff, ← hgen]
  refine Subgroup.closure_mono ?_
  rintro g (((hg | hg) | hg) | hg)
  · exact ⟨A₁, hA₁E, by rw [hA₁]; exact hne1, hg⟩
  · exact ⟨A₂, hA₂E, by rw [hA₂]; exact he₂1, hg⟩
  · exact ⟨A₁ * A₂, hB3E, by rw [map_mul, hA₁, hA₂]; simpa using hne 1, hg⟩
  · exact ⟨A₁ * A₂ ^ 2, hB4E, by rw [map_mul, map_pow, hA₁, hA₂]; exact hne 2, hg⟩

theorem unitaryOuterAbTwo_holds : UnitaryOuterAbTwo := by
  intro K _ h n hn4 hn3 E hE hc hD _ hab
  exact planeGen_of_diag_abelian_two h (by norm_num) (by omega) hE hc hD hab

end CFSG.LieType.SeitzGeneration
