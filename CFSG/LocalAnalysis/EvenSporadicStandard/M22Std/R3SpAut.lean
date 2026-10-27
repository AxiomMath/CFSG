module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SpAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SpH90
public import CFSG.LocalAnalysis.SteinbergCCSymplecticFourCenterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SpAssemble
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis

variable {X : Type} [Group X] {E : Subgroup X} {z : X} {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def spU (ψ : E ≃* antiSp K) : Subgroup X :=
  ((antiUnipotent K).map ψ.symm.toMonoidHom).map E.subtype

omit [Finite K] in
theorem mem_spU {ψ : E ≃* antiSp K} {u : X} :
    u ∈ spU ψ ↔ ∃ hu : u ∈ E, ψ ⟨u, hu⟩ ∈ antiUnipotent K := by
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e.2, ?_⟩
    have he' : e ∈ (antiUnipotent K).map ψ.symm.toMonoidHom := he
    rw [Subgroup.mem_map_equiv] at he'
    simpa using he'
  · rintro ⟨hu, h⟩
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    show (⟨u, hu⟩ : E) ∈ (antiUnipotent K).map ψ.symm.toMonoidHom
    rw [Subgroup.mem_map_equiv]
    simpa using h

omit [Finite K] in
theorem spU_le (ψ : E ≃* antiSp K) : spU ψ ≤ E := fun _ hu => (mem_spU.1 hu).1

theorem card_spU (hK : Nat.card K = 4) (ψ : E ≃* antiSp K) : Nat.card (spU ψ) = 256 := by
  have h1 : Nat.card (spU ψ) = Nat.card ((antiUnipotent K).map ψ.symm.toMonoidHom) :=
    Subgroup.card_map_of_injective E.subtype_injective
  rw [h1, Subgroup.card_map_of_injective ψ.symm.injective, card_and_isSylowTwoOf_antiUnipotent.1,
    hK]
  norm_num

theorem card_of_equiv_antiSp (hK : Nat.card K = 4) (ψ : E ≃* antiSp K) :
    Nat.card E = 979200 := by
  rw [Nat.card_congr ψ.toEquiv, card_antiSp hK]
  norm_num

theorem isSylowOf_spU [Finite X] (hK : Nat.card K = 4) (ψ : E ≃* antiSp K) :
    IsSylowOf 2 (spU ψ) E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card (spU_le ψ) ?_
  rw [card_spU hK ψ, card_of_equiv_antiSp hK ψ]
  have h : (979200 : ℕ).factorization 2 = 8 := by
    have h1 : (979200 : ℕ) = 2 ^ 8 * 3825 := by norm_num
    rw [h1, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have : (3825 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [this]
  rw [h]
  norm_num

theorem spU_stable {ψ : E ≃* antiSp K}
    (hact : ∀ (e : E) (he : z * (e : X) * z⁻¹ ∈ E), ψ ⟨z * e * z⁻¹, he⟩ = frobAut K (ψ e))
    (hn : ∀ e ∈ E, z * e * z⁻¹ ∈ E) {u : X} (hu : u ∈ spU ψ) : z * u * z⁻¹ ∈ spU ψ := by
  obtain ⟨huE, hU0⟩ := mem_spU.1 hu
  refine mem_spU.2 ⟨hn u huE, ?_⟩
  rw [hact ⟨u, huE⟩ (hn u huE)]
  exact frobAut_mem_antiUnipotent hU0

theorem spU_h90 (hK : Nat.card K = 4) {ψ : E ≃* antiSp K}
    (hact : ∀ (e : E) (he : z * (e : X) * z⁻¹ ∈ E), ψ ⟨z * e * z⁻¹, he⟩ = frobAut K (ψ e))
    (hn : ∀ e ∈ E, z * e * z⁻¹ ∈ E) {u : X} (hu : u ∈ spU ψ) (hc : u * (z * u * z⁻¹) = 1) :
    ∃ v ∈ spU ψ, u = v⁻¹ * (z * v * z⁻¹) := by
  obtain ⟨huE, hU0⟩ := mem_spU.1 hu
  have hzu := hn u huE
  have h1 : ψ ⟨u, huE⟩ * frobAut K (ψ ⟨u, huE⟩) = 1 := by
    rw [← hact ⟨u, huE⟩ hzu, ← map_mul]
    have : (⟨u, huE⟩ : E) * ⟨z * u * z⁻¹, hzu⟩ = 1 := Subtype.ext hc
    rw [this, map_one]
  obtain ⟨v0, hv0U, hv0⟩ := antiUnipotent_h90 hK hU0 h1
  have hvE : ((ψ.symm v0 : E) : X) ∈ E := (ψ.symm v0).2
  have hvU : ((ψ.symm v0 : E) : X) ∈ spU ψ :=
    mem_spU.2 ⟨hvE, by simpa using hv0U⟩
  refine ⟨_, hvU, ?_⟩
  have h2 : ψ ⟨z * ((ψ.symm v0 : E) : X) * z⁻¹, hn _ hvE⟩ = frobAut K v0 := by
    rw [hact (ψ.symm v0) (hn _ hvE)]
    simp
  have h3 : (⟨u, huE⟩ : E) = (ψ.symm v0)⁻¹ * ⟨z * ((ψ.symm v0 : E) : X) * z⁻¹, hn _ hvE⟩ := by
    apply ψ.injective
    rw [map_mul, map_inv, h2]
    simp
    exact hv0
  exact congrArg Subtype.val h3

theorem card_centralizer_of_involution [Finite X] (hK : Nat.card K = 4) (ψ : E ≃* antiSp K)
    {q : X} (hq : q ∈ E) (hq2 : q * q = 1) : 256 ∣ Nat.card (centralizer ({q} : Set X)) := by
  have hq0 : ψ ⟨q, hq⟩ * ψ ⟨q, hq⟩ = 1 := by
    rw [← map_mul]
    have : (⟨q, hq⟩ : E) * ⟨q, hq⟩ = 1 := Subtype.ext hq2
    rw [this, map_one]
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.SymplecticFourFusion.exists_conj_mem_center hq0
  have hcent := (mem_antiUnipotentCenter_iff_central _).1 hg
  set ψ2 : E ≃* antiSp K := ψ.trans (MulAut.conj g) with hψ2
  have hle : spU ψ2 ≤ centralizer ({q} : Set X) := by
    intro u hu
    obtain ⟨huE, hU0⟩ := mem_spU.1 hu
    rw [mem_centralizer_singleton_iff]
    have h1 := hcent.2 _ hU0
    have h2 : ψ ⟨u, huE⟩ * ψ ⟨q, hq⟩ = ψ ⟨q, hq⟩ * ψ ⟨u, huE⟩ := by
      have h3 : (g * ψ ⟨u, huE⟩ * g⁻¹) * (g * ψ ⟨q, hq⟩ * g⁻¹) =
          (g * ψ ⟨q, hq⟩ * g⁻¹) * (g * ψ ⟨u, huE⟩ * g⁻¹) := h1.symm
      have h4 : g * (ψ ⟨u, huE⟩ * ψ ⟨q, hq⟩) * g⁻¹ = g * (ψ ⟨q, hq⟩ * ψ ⟨u, huE⟩) * g⁻¹ := by
        calc g * (ψ ⟨u, huE⟩ * ψ ⟨q, hq⟩) * g⁻¹
            = (g * ψ ⟨u, huE⟩ * g⁻¹) * (g * ψ ⟨q, hq⟩ * g⁻¹) := by group
          _ = (g * ψ ⟨q, hq⟩ * g⁻¹) * (g * ψ ⟨u, huE⟩ * g⁻¹) := h3
          _ = g * (ψ ⟨q, hq⟩ * ψ ⟨u, huE⟩) * g⁻¹ := by group
      simpa using h4
    have h5 : (⟨u, huE⟩ : E) * ⟨q, hq⟩ = ⟨q, hq⟩ * ⟨u, huE⟩ := by
      apply ψ.injective
      rw [map_mul, map_mul]
      exact h2
    exact congrArg Subtype.val h5
  have := Subgroup.card_dvd_of_le hle
  rwa [card_spU hK ψ2] at this

theorem outerWr1_of_equiv [Finite X] (hK : Nat.card K = 4) (hz2 : z * z = 1) (hzE : z ∉ E)
    (hn : ∀ e ∈ E, z * e * z⁻¹ ∈ E) (ψ : E ≃* antiSp K)
    (hact : ∀ (e : E) (he : z * (e : X) * z⁻¹ ∈ E), ψ ⟨z * e * z⁻¹, he⟩ = frobAut K (ψ e))
    (hCz : centralizer ({z} : Set X) ≤ extSub E z hz2 hn) :
    OuterWr1 X z (extSub E z hz2 hn) E := by
  refine ⟨z_mem_extSub, hCz, le_extSub, hzE, fun x hx => hx, ?_, ?_⟩
  · intro q hq hq2 _
    exact dvd_trans (by norm_num) (card_centralizer_of_involution hK ψ hq hq2)
  · intro P hP hzP y hyP hy2 hyE
    exact exists_conj_of_h90 hz2 hzE hn (spU_le ψ) (isSylowOf_spU hK ψ)
      (fun u hu => spU_stable hact hn hu) (fun u hu hc => spU_h90 hK hact hn hu hc) hP hzP hyP
      hy2 hyE

end CFSG.EvenSporadicStandard.M22Std
