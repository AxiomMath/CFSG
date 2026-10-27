module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUCat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceTools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA10Out
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFa
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFb
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NoPump
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7OS1
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3e
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3f
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3g
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4h
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SecL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBSections
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAssembly
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
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
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace QPUJ

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_center_of_isComponent (hO : pPrimeCore 2 G = ⊥) {M : Subgroup G}
    (hM : IsComponent M) : IsPGroup 2 (center ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x
  obtain ⟨c₂, hc₂, c₂', hc₂', hcc, ⟨k, hk⟩, hodd⟩ := NF58.exists_two_part_mul_odd (x : ↥M)
  have hc₂'Z : c₂' ∈ center ↥M := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc₂'
    exact zpow_mem x.2 n
  set N : Subgroup G := (zpowers c₂').map M.subtype with hN
  have hNM : N ≤ M := map_subtype_le _
  have hNn : (N.subgroupOf M).Normal := by
    rw [hN, show ((zpowers c₂').map M.subtype).subgroupOf M = zpowers c₂' from
      comap_map_eq_self_of_injective M.subtype_injective _]
    constructor
    intro n hn g
    rw [show g * n * g⁻¹ = n by rw [mem_center_iff.mp (zpowers_le.mpr hc₂'Z hn) g]; group]
    exact hn
  have hNs : N.IsSubnormal := Subgroup.IsSubnormal.trans hNM hNn.isSubnormal hM.2
  have hcop : Nat.Coprime 2 (Nat.card N) := by
    rw [hN, card_map_of_injective M.subtype_injective, Nat.card_zpowers]
    exact Nat.coprime_two_left.mpr hodd
  have hNb := RankThree.PartOne.Sec1511.le_pPrimeCore_of_isSubnormal_p hNs hcop
  rw [hO] at hNb
  have h1 : c₂' = 1 := by
    have h2 : (c₂' : G) ∈ N := mem_map_of_mem _ (mem_zpowers c₂')
    exact Subtype.ext (mem_bot.mp (hNb h2))
  rw [h1, mul_one] at hcc
  refine ⟨k, Subtype.ext ?_⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hcc]
  exact hk

theorem config_of_component (hO : pPrimeCore 2 G = ⊥) {M : Subgroup G} (hM : IsComponent M)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPM : P ≤ normalizer (M : Set G))
    {L : Subgroup G} (hLM : L ≤ M) (hLC : L ≤ centralizer (P : Set G))
    (hLpc : IsPComponent 2 (L.subgroupOf (centralizer (P : Set G)))) (hLne : L ≠ M)
    {p' f' p f : ℕ} (hp' : p'.Prime) (hp2' : p' ≠ 2) (hf' : 1 ≤ f') (h5' : 5 ≤ p' ^ f')
    (hLLie : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p' f')
    {t : G} (htL : t ∈ L) (ht2 : t * t = 1) (htZ : ∃ m ∈ M, m * t ≠ t * m)
    {J : Subgroup G} (hJM : J ≤ M) (hJC : J ≤ centralizer ({t} : Set G))
    (hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set G))))
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f) (hpp : p = p') (hff : f = f')
    (hJLie : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f)
    {J₀ : Subgroup G} (hJ₀L : J₀ ≤ L) (hJ₀J : J₀ ≤ J)
    (hJ₀ : J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) :
    QPUJConfig ↥M p' f' p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hM.1, isPGroup_center_of_isComponent hO hM, hp', hp2', hf', h5', hp, hp2, hf, h5, hpp,
    hff, ?_⟩
  set E : Subgroup (MulAut ↥M) :=
    (P.subgroupOf (normalizer (M : Set G))).map M.normalizerMonoidHom with hE
  have hE2 : IsPGroup 2 E := (hP.comap_subtype).map _
  have hfix : autFixed E = (M ⊓ centralizer (P : Set G)).subgroupOf M := by
    ext m
    rw [mem_autFixed, mem_subgroupOf, mem_inf]
    constructor
    · intro h
      refine ⟨m.2, mem_centralizer_iff.mpr fun β hβ => ?_⟩
      have h1 := h (M.normalizerMonoidHom ⟨β, hPM hβ⟩)
        (mem_map_of_mem _ (show (⟨β, hPM hβ⟩ : ↥(normalizer (M : Set G))) ∈
          P.subgroupOf (normalizer (M : Set G)) from mem_subgroupOf.mpr hβ))
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      calc β * (m : G) = β * (m : G) * β⁻¹ * β := by group
        _ = (m : G) * β := by rw [h2]
    · rintro ⟨-, hmC⟩ e ⟨⟨β, hβN⟩, hβ, rfl⟩
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      show β * (m : G) * β⁻¹ = m
      rw [mem_centralizer_iff.mp hmC β (mem_subgroupOf.mp hβ)]
      group
  have hCt : centralizer ({(⟨t, hLM htL⟩ : ↥M)} : Set ↥M) =
      (M ⊓ centralizer ({t} : Set G)).subgroupOf M := by
    ext m
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨m.2, congrArg Subtype.val h⟩, fun h => Subtype.ext h.2⟩
  have htrans : ∀ {A D : Subgroup G}, A ≤ D → D ≤ M → IsPComponent 2 (A.subgroupOf D) →
      IsPComponent 2 ((A.subgroupOf M).subgroupOf (D.subgroupOf M)) := by
    intro A D hAD hDM hA
    have hAM := hAD.trans hDM
    rw [← OddStandard.Solomon75.isPComponent_subgroupOf_map_iff 2 M.subtype M.subtype_injective
      (fun x hx => mem_subgroupOf.mpr (hAD (mem_subgroupOf.mp hx))),
      map_subgroupOf_eq_of_le hAM, map_subgroupOf_eq_of_le hDM]
    exact hA
  have hlie : ∀ {A : Subgroup G} {τ : Assembly.LowTwoRank.StatedLieTag} {n r e : ℕ}, A ≤ M →
      Blueprint.LieModel (↥A ⧸ pPrimeCore 2 ↥A) τ n r e →
      Blueprint.LieModel (↥(A.subgroupOf M) ⧸ pPrimeCore 2 ↥(A.subgroupOf M)) τ n r e :=
    fun hAM h => OddQuot.lieModel_of_equiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hAM).symm) h
  refine ⟨E, L.subgroupOf M, ⟨t, hLM htL⟩, J.subgroupOf M, J₀.subgroupOf M, hE2, ?_, ?_, ?_,
    hlie hLM hLLie, mem_subgroupOf.mpr htL, Subtype.ext ht2, ?_, ?_, ?_, hlie hJM hJLie,
    fun x hx => mem_subgroupOf.mpr (hJ₀L (mem_subgroupOf.mp hx)),
    fun x hx => mem_subgroupOf.mpr (hJ₀J (mem_subgroupOf.mp hx)), ?_⟩
  ·
    rw [hfix]
    intro l hl
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨l.2, hLC (mem_subgroupOf.mp hl)⟩)
  ·
    rw [hfix]
    exact htrans (le_inf hLM hLC) inf_le_left
      (OddStandard.Solomon75.isPComponent_subgroupOf_mono (le_inf hLM hLC) inf_le_right hLpc)
  ·
    intro h
    apply hLne
    refine le_antisymm hLM fun m hm => ?_
    have h1 : (⟨m, hm⟩ : ↥M) ∈ L.subgroupOf M := h ▸ mem_top _
    exact mem_subgroupOf.mp h1
  ·
    intro h
    obtain ⟨m, hmM, hm⟩ := htZ
    exact hm (congrArg Subtype.val (mem_center_iff.mp h ⟨m, hmM⟩))
  ·
    rw [hCt]
    intro j hj
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨j.2, hJC (mem_subgroupOf.mp hj)⟩)
  ·
    rw [hCt]
    exact htrans (le_inf hJM hJC) inf_le_left
      (OddStandard.Solomon75.isPComponent_subgroupOf_mono (le_inf hJM hJC) inf_le_right hJpc)
  ·
    apply map_injective M.subtype_injective
    have hcomp : M.subtype.comp (J.subgroupOf M).subtype =
        J.subtype.comp (subgroupOfEquivOfLe hJM).toMonoidHom := by
      ext x
      rfl
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (hJ₀J.trans hJM), map_subgroupOf_eq_of_le hJM,
      map_map, hcomp, ← map_map, pPrimeCore_map_iso]
    exact hJ₀

end QPUJ

end CFSG.ComponentClassification.GSThmB
