module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallThreeOrders
public import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
public import CFSG.RankThree.PartTwo.KFacts.L34CenterProof
public import CFSG.ClassicalInvolution.Q3.TwinLemmaBasic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Foundations
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.T444.Step451
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.Assembly.RankThreeEven

variable {G : Type} [Group G] [Finite G]

local notation "Y" => primeComplementCore (G := G) 3

omit [Finite G] in
theorem isSimpleGroup_quotient (hLY : AGLEmbedding.IsLinThreeFour (G ⧸ Y)) :
    IsSimpleGroup (G ⧸ Y) := by
  obtain ⟨e⟩ := AGLEmbedding.KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hLY
  have := CFSG.RankThree.PartTwo.Sec4.isSimpleGroup_projSL
  exact e.isSimpleGroup

omit [Finite G] in
theorem center_quotient_eq_bot (hLY : AGLEmbedding.IsLinThreeFour (G ⧸ Y)) :
    center (G ⧸ Y) = ⊥ := by
  obtain ⟨e⟩ := AGLEmbedding.KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hLY
  have h := CFSG.RankThree.PartTwo.Sec4.center_projSL_eq_bot
  rw [← Subgroup.map_center_eq e.symm, h, Subgroup.map_bot]

omit [Finite G] in
theorem card_quotient (hLY : AGLEmbedding.IsLinThreeFour (G ⧸ Y)) :
    Nat.card (G ⧸ Y) = 20160 :=
  AGLEmbedding.card_of_isLinThreeFour hLY

theorem pCore_three_eq_bot (hLY : AGLEmbedding.IsLinThreeFour (G ⧸ Y)) :
    CFSG.pCore 3 G = ⊥ := by
  have := isSimpleGroup_quotient hLY
  have hP : IsPGroup 3 (CFSG.pCore 3 G) := CFSG.pCore_isPGroup
  have : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal
  have hmapN : ((CFSG.pCore 3 G).map (QuotientGroup.mk' Y)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Y)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 3 G).map (QuotientGroup.mk' Y))
    with h | h
  ·
    have hle : CFSG.pCore 3 G ≤ Y := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 3 G)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) (primeComplementCore_coprime 3)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases hP.card_eq_or_dvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  ·
    exfalso
    have hq : IsPGroup 3 (G ⧸ Y) := by
      intro q
      have hq' : q ∈ (CFSG.pCore 3 G).map (QuotientGroup.mk' Y) := h ▸ Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq'
      obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
      refine ⟨k, ?_⟩
      have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [← map_pow, hk', map_one]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hq.exists_card_eq
    rw [card_quotient hLY] at hk
    have h2 : (2 : ℕ) ∣ 3 ^ k := hk ▸ (by norm_num : (2 : ℕ) ∣ 20160)
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    omega

omit [Finite G] in
theorem component_le_or_sup_eq_top (hLY : AGLEmbedding.IsLinThreeFour (G ⧸ Y))
    {K : Subgroup G} (hK : CFSG.IsComponent K) : K ≤ Y ∨ K ⊔ Y = ⊤ := by
  have := isSimpleGroup_quotient hLY
  have hsn : (K.map (QuotientGroup.mk' Y)).IsSubnormal :=
    hK.2.map (QuotientGroup.mk'_surjective Y)
  rcases hsn.eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    have := Subgroup.comap_map_eq (QuotientGroup.mk' Y) K
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    exact this.symm

theorem nonempty_mulEquiv_quotient_of_sup_eq_top
    (hLY : AGLEmbedding.IsLinThreeFour (G ⧸ Y))
    (hO2 : CFSG.pCore 2 G = ⊥) {K : Subgroup G} (hK : CFSG.IsComponent K) (hKY : K ⊔ Y = ⊤) :
    Nonempty (↥K ≃* G ⧸ Y) := by
  classical
  have hsimp := isSimpleGroup_quotient hLY
  set π : G →* G ⧸ Y := QuotientGroup.mk' Y with hπ
  set φ : ↥K →* G ⧸ Y := π.comp K.subtype with hφ
  have hmapK : K.map π = ⊤ := by
    have h := congrArg (Subgroup.map π) hKY
    rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective Y),
      hπ, QuotientGroup.map_mk'_self, sup_bot_eq] at h
  have hφs : Function.Surjective φ := by
    intro q
    have hq : q ∈ K.map π := by rw [hmapK]; trivial
    obtain ⟨k, hk, rfl⟩ := hq
    exact ⟨⟨k, hk⟩, rfl⟩
  have hkerφ : φ.ker = (Y).subgroupOf K := by
    ext k
    simp [hφ, hπ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hZY : ∀ z : ↥K, z ∈ center ↥K → (z : G) ∈ Y := by
    intro z hz
    have hcent : φ z ∈ center (G ⧸ Y) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨k, rfl⟩ := hφs q
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz k)]
    rw [center_quotient_eq_bot hLY, Subgroup.mem_bot] at hcent
    have : z ∈ φ.ker := hcent
    rw [hkerφ, Subgroup.mem_subgroupOf] at this
    exact this
  have hYK : (Y).subgroupOf K ≤ center ↥K := by
    have hN : ((Y).subgroupOf K).Normal := Subgroup.Normal.subgroupOf inferInstance K
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hN with h | h
    · exfalso
      have hKle : K ≤ Y := by
        intro k hk
        have : (⟨k, hk⟩ : ↥K) ∈ (Y).subgroupOf K := by rw [h]; trivial
        exact this
      have hYtop : Y = ⊤ := by rw [← hKY, sup_eq_right.mpr hKle]
      have hnt := hsimp.toNontrivial
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      apply hab
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, hYtop]
      trivial
    · exact h
  have hZeq : center ↥K = (Y).subgroupOf K := by
    refine le_antisymm (fun z hz => ?_) hYK
    rw [Subgroup.mem_subgroupOf]
    exact hZY z hz
  have hKZ : Nonempty (↥K ⧸ center ↥K ≃* projSL 3 (GaloisField 2 2)) := by
    obtain ⟨e⟩ := AGLEmbedding.KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hLY
    refine ⟨((QuotientGroup.quotientMulEquivOfEq (hZeq.trans hkerφ.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).trans e⟩
  have hZ3 : ¬ 3 ∣ Nat.card (center ↥K) := by
    have hcop : Nat.Coprime 3 (Nat.card (center ↥K)) := by
      have hle : (center ↥K).map K.subtype ≤ Y := by
        rintro _ ⟨z, hz, rfl⟩
        exact hZY z hz
      have h1 : Nat.card (center ↥K) = Nat.card ((center ↥K).map K.subtype) :=
        Nat.card_congr (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).toEquiv
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
        (primeComplementCore_coprime 3)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  have hZ2 : IsPGroup 2 (center ↥K) :=
    CFSG.RankThree.PartTwo.KFacts.l34CenterThreePrimeTwo ↥K hK.1 hKZ (center ↥K) le_rfl hZ3
  have hZbot : center ↥K = ⊥ := by
    have hsn : ((center ↥K).map K.subtype).IsSubnormal :=
      Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hK.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle := CFSG.ClassicalInvolution.Q3.Twin.le_pCore_of_isSubnormal hsn (hZ2.map _)
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hle
    exact hle
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hkerφ, ← hZeq, hZbot]
  exact ⟨MulEquiv.ofBijective φ ⟨hφi, hφs⟩⟩

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
