module

public import CFSG.GH74.Uniqueness.SU.SU10Prod
public import CFSG.GH74.Uniqueness.SU.SU10Bar
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.L5U5.ModelsBridge
public import CFSG.GH74.Statements
public import CFSG.GH74.Uniqueness.SU.SU0GH
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.SectionRank.CentralLift
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
public import CFSG.Walter.JRAssembly
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_top (S : Sylow 2 G) : IsSylowIn ⊤ (S : Subgroup G) := by
  refine ⟨le_top, S.isPGroup', ?_⟩
  have hdvd : (S : Subgroup G).relIndex ⊤ = (S : Subgroup G).index :=
    Subgroup.relIndex_top_right _
  rw [hdvd]
  exact Nat.not_even_iff_odd.mp fun hev => S.not_dvd_index (even_iff_two_dvd.mp hev)

theorem exists_isSylowIn (X : Subgroup G) : ∃ P : Subgroup G, IsSylowIn X P := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥X) := inferInstance
  refine ⟨(Q : Subgroup ↥X).map X.subtype, Subgroup.map_subtype_le _,
    Q.isPGroup'.map X.subtype, ?_⟩
  have h0 : ((Q : Subgroup ↥X).map X.subtype).subgroupOf X = (Q : Subgroup ↥X) := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h1 : ((Q : Subgroup ↥X).map X.subtype).relIndex X = (Q : Subgroup ↥X).index := by
    rw [Subgroup.relIndex, h0]
  rw [h1]
  exact Nat.not_even_iff_odd.mp fun hev => Q.not_dvd_index (even_iff_two_dvd.mp hev)

theorem exists_conj_le {X P K : Subgroup G} (hP : IsSylowIn X P) (hKX : K ≤ X)
    (hK : IsPGroup 2 K) : ∃ x ∈ X, K ≤ P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨Q, hQ⟩ := (hK.comap_subtype (K := X)).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥X (sylowIn hP) Q
  refine ⟨x, x.2, fun k hk => ?_⟩
  have hkQ : (⟨k, hKX hk⟩ : ↥X) ∈ (Q : Subgroup ↥X) := hQ hk
  have hmem : MulAut.conj x⁻¹ • (⟨k, hKX hk⟩ : ↥X) ∈ ((x⁻¹ • Q : Sylow 2 ↥X) : Subgroup ↥X) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hkQ
  have hxx : x⁻¹ • Q = sylowIn hP := by rw [← hx, inv_smul_smul]
  rw [hxx, coe_sylowIn, Subgroup.mem_subgroupOf] at hmem
  have h2 : (x : G)⁻¹ * k * (x : G) ∈ P := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hmem
  refine ⟨(x : G)⁻¹ * k * (x : G), h2, ?_⟩
  show (x : G) * ((x : G)⁻¹ * k * (x : G)) * (x : G)⁻¹ = k
  group

omit [Finite G] in
theorem isSylowIn_of_le {X P P₁ : Subgroup G} (hP : IsSylowIn X P) (hPP₁ : P ≤ P₁)
    (hP₁X : P₁ ≤ X) (hP₁ : IsPGroup 2 P₁) : IsSylowIn X P₁ := by
  refine ⟨hP₁X, hP₁, ?_⟩
  have h := Subgroup.relIndex_dvd_of_le_left X hPP₁
  exact Nat.not_even_iff_odd.mp fun hev =>
    (Nat.not_even_iff_odd.mpr hP.2.2) (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hev) h))

theorem pRank_eq_of_isSylowIn {X P : Subgroup G} (hP : IsSylowIn X P) :
    Open.pRank 2 P = Open.pRank 2 X := by
  apply le_antisymm (SU1.pRank_mono (by norm_num) hP.1)
  obtain ⟨E, hEX, hE, hcard⟩ := SU1.exists_pRank (p := 2) (by norm_num) X
  have hEp : IsPGroup 2 E := fun g => ⟨1, by
    have := (SU1.isElemAbelian_iff.mp hE).2 g.1 g.2
    apply Subtype.ext
    simpa using this⟩
  obtain ⟨x, -, hxE⟩ := exists_conj_le hP hEX hEp
  have h1 : E.map (MulAut.conj x⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨p, hp, hpe⟩ := hxE he
    have hpe' : x * p * x⁻¹ = e := hpe
    have : (MulAut.conj x⁻¹).toMonoidHom e = p := by
      show x⁻¹ * e * x⁻¹⁻¹ = p
      rw [← hpe']
      group
    rw [this]
    exact hp
  have h2 : Open.IsElemAbelian 2 (E.map (MulAut.conj x⁻¹).toMonoidHom) := isElemAbelian_map hE
  have h3 : Nat.card (E.map (MulAut.conj x⁻¹).toMonoidHom) = 2 ^ Open.pRank 2 X := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hcard]
  exact SU1.le_pRank (by norm_num) h1 h2 h3

omit [Finite G] in
theorem centralizer_singleton_conj (k u : G) :
    centralizer ({k * u * k⁻¹} : Set G) =
      (centralizer ({u} : Set G)).map (MulAut.conj k).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc k⁻¹ * x * k * u = k⁻¹ * (x * (k * u * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * u * k⁻¹) * x) * k := by rw [h]
        _ = u * (k⁻¹ * x * k) := by group
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    show k * y * k⁻¹ * (k * u * k⁻¹) = k * u * k⁻¹ * (k * y * k⁻¹)
    calc k * y * k⁻¹ * (k * u * k⁻¹) = k * (y * u) * k⁻¹ := by group
      _ = k * (u * y) * k⁻¹ := by rw [hyu]
      _ = k * u * k⁻¹ * (k * y * k⁻¹) := by group

omit [Finite G] in
theorem isSylowIn_conj {X P : Subgroup G} (hP : IsSylowIn X P) (g : G) :
    IsSylowIn (X.map (MulAut.conj g).toMonoidHom) (P.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Subgroup.map_mono hP.1, hP.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hP.2.2

theorem exists_extremal_conj (S : Sylow 2 G) {u : G} (hu : orderOf u = 2) :
    ∃ k : G, k * u * k⁻¹ ∈ (S : Subgroup G) ∧
      IsSylowIn (centralizer ({k * u * k⁻¹} : Set G))
        ((S : Subgroup G) ⊓ centralizer ({k * u * k⁻¹} : Set G)) := by
  obtain ⟨T, hT⟩ := exists_isSylowIn (centralizer ({u} : Set G))
  have huC : u ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have huT : u ∈ T := by
    have hzp : IsPGroup 2 (zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; simp)
    obtain ⟨x, hxC, hx⟩ := exists_conj_le hT (K := zpowers u) (Subgroup.zpowers_le.mpr huC) hzp
    obtain ⟨p, hp, hpu⟩ := hx (Subgroup.mem_zpowers u)
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have h1 : x * p * x⁻¹ = u := hpu
    have : p = u := by
      calc p = x⁻¹ * (x * p * x⁻¹) * x := by group
        _ = x⁻¹ * u * x := by rw [h1]
        _ = u := by
          calc x⁻¹ * u * x = x⁻¹ * (u * x) := mul_assoc _ _ _
            _ = x⁻¹ * (x * u) := by rw [hxu]
            _ = u := inv_mul_cancel_left _ _
    rwa [← this]
  obtain ⟨x, -, hxS⟩ := exists_conj_le (isSylowIn_top S) (le_top) hT.2.1
  have hTS : ∀ t ∈ T, x⁻¹ * t * x ∈ (S : Subgroup G) := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := hxS ht
    have : (MulAut.conj x).toMonoidHom s = x * s * x⁻¹ := rfl
    rw [this] at hst
    have h2 : x⁻¹ * t * x = s := by rw [← hst]; group
    rw [h2]
    exact hs
  have hk : x⁻¹ * u * x⁻¹⁻¹ ∈ (S : Subgroup G) := by
    simpa using hTS u huT
  refine ⟨x⁻¹, hk, ?_⟩
  have hT₁ := isSylowIn_conj hT x⁻¹
  rw [← centralizer_singleton_conj] at hT₁
  have hT₁S : T.map (MulAut.conj x⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rintro _ ⟨t, ht, rfl⟩
    simpa using hTS t ht
  have hle : T.map (MulAut.conj x⁻¹).toMonoidHom ≤
      (S : Subgroup G) ⊓ centralizer ({x⁻¹ * u * x⁻¹⁻¹} : Set G) := le_inf hT₁S hT₁.1
  exact isSylowIn_of_le hT₁ hle inf_le_right (S.isPGroup'.to_inf_left)

end CFSG.GH74.Uniqueness.SU.SU10
