module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Ord
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11AltMain
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.Sporadic.SuzOddCore.ExtModel
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterProjective
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.Walter.AStar.Subnormal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.CharacterTheory.Wreathed.OddLinearTwoAutomorphisms
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11R
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeNormalExtension
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

namespace CFSG.ComponentClassification.GSThmB.X11

open CFSG Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem isPComponent_of_map_eq {b : G} {K : Subgroup G} (hKN : K ≤ N)
    (hKb : K ≤ centralizer ({b} : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set G)))) {Y : Subgroup ↥N}
    (hY : Y.map N.subtype = centralizer ({b} : Set G) ⊓ N) :
    K.subgroupOf N ≤ Y ∧ IsPComponent 2 ((K.subgroupOf N).subgroupOf Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun y hy => ?_, ?_⟩
  · have h1 : (y : G) ∈ Y.map N.subtype := by
      rw [hY]
      exact ⟨hKb (mem_subgroupOf.mp hy), y.2⟩
    obtain ⟨z, hz, hzy⟩ := h1
    rwa [N.subtype_injective hzy] at hz
  · rw [Burgoyne.isPComponent_subgroupOf_map_iff 2 Nat.prime_two N.subtype_injective, hY,
      subgroupOf_map_subtype, inf_eq_left.mpr hKN]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKb hKN) inf_le_left hKc

omit [Finite G] in
theorem KConf.nonabelian (h : KConf G N) : ∃ x y : ↥N, x * y ≠ y * x := by
  obtain ⟨-, hC, hs, b, K, hb, hKN, hKb, -, hKm⟩ := h
  by_contra hcon
  push Not at hcon
  have hnorm : (K.subgroupOf N).Normal :=
    ⟨fun x hx g => by rwa [hcon g x, mul_inv_cancel_right]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf N) with h1 | h1
  · have hK1 : Nat.card ↥K = 1 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv, h1, card_bot]
    have := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥K)
    rw [card_of_lieModel_psp_four_three hKm, hK1] at this
    exact absurd (Nat.le_of_dvd one_pos this) (by norm_num)
  · have hbC : b ∈ centralizer (N : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have hxK : (⟨x, hx⟩ : ↥N) ∈ K.subgroupOf N := h1 ▸ mem_top _
      exact mem_centralizer_singleton_iff.mp (hKb hxK)
    rw [hC, mem_bot] at hbC
    rw [hbC, orderOf_one] at hb
    exact absurd hb (by norm_num)

theorem isComponent_of_equiv {X : Type*} [Group X] [Finite X] {B : Subgroup X} (hB : B.IsSubnormal)
    {S : Type*} [Group S] [IsSimpleGroup S] [Finite S] (e : ↥B ≃* S) (hS : Nat.card S = 25920) :
    IsComponent B ∧ Nat.card (↥B ⧸ center ↥B) = 25920 := by
  have : IsSimpleGroup ↥B := (MulEquiv.isSimpleGroup_congr e).mpr inferInstance
  obtain ⟨x, y, hxy⟩ := Sym.exists_ne_of_card hS
  have hna : ∃ a b : ↥B, a * b ≠ b * a :=
    ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
  refine ⟨⟨hq, hB⟩, ?_⟩
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv,
    Nat.card_congr QuotientGroup.quotientBot.toEquiv, Nat.card_congr e.toEquiv, hS]

theorem KConf.not_suz
    (hSuzO : SolMax.SuzOuterComponentsInput) (h : KConf G N) :
    ¬ Blueprint.NativeSporadic.IsSporadic ↥N .Suz := by
  rintro ⟨ψ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hna := h.nonabelian
  obtain ⟨hNn, hC, hs, b, K, hb, hKN, hKb, hKc, hKm⟩ := h
  have hF : generalizedFitting G = N :=
    Wreathed.DegreeThreeModelFullCenter.generalizedFitting_eq_of_selfCentralizing_simple_normal
      N hNn hna hC
  have hsF : IsSimpleGroup ↥(generalizedFitting G) := by rw [hF]; exact hs
  have hnaF : ∃ x y : ↥(generalizedFitting G), x * y ≠ y * x := by rw [hF]; exact hna
  have hO := (Sporadic.SuzOddCore.CTUC_Suz_model_simple_generalized_fitting_centralizer_exclusion
    hsF hnaF ((MulEquiv.subgroupCongr hF).trans ψ)).2 b hb
  rw [ABGDGroups.oddCore_eq_pPrimeCore_two] at hO
  set K₀ := K.subgroupOf (centralizer ({b} : Set G)) with hK₀
  have hK₀s : K₀.IsSubnormal := hKc.choose_spec.2.1
  have hOK₀ : pPrimeCore 2 ↥K₀ = ⊥ := by
    have h1 := Walter.map_pPrimeCore_le_of_isSubnormal hK₀s
    rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ K₀.subtype_injective] at h1
    exact h1
  have hOK : pPrimeCore 2 ↥K = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hKb)
    rw [hOK₀, Subgroup.map_bot] at h1
    exact h1.symm
  have hQs : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 3 1
      (GH74.statedClassicalModel_of_lieModel (by norm_num) hKm)
  have hQc := card_of_lieModel_psp_four_three hKm
  let eK : ↥K ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOK.symm))
  by_cases hbN : b ∈ N
  ·
    set a : ↥N := ⟨b, hbN⟩
    have hY : (centralizer ({a} : Set ↥N)).map N.subtype = centralizer ({b} : Set G) ⊓ N := by
      ext x
      simp only [mem_map, mem_inf, subtype_apply, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨congrArg Subtype.val hy, y.2⟩
      · rintro ⟨hx, hxN⟩
        exact ⟨⟨x, hxN⟩, Subtype.ext hx, rfl⟩
    obtain ⟨hle, hP⟩ := isPComponent_of_map_eq hKN hKb hKc hY
    have ha : orderOf a = 2 := by rw [Subgroup.orderOf_mk, hb]
    obtain ⟨hcomp, hcard⟩ := isComponent_of_equiv (B := (K.subgroupOf N).subgroupOf _)
      hP.choose_spec.2.1 (((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hKN)).trans eK)
      hQc
    have := Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order ψ a ha
      _ hcomp
    omega
  ·
    let σ : MulAut ↥N := MulAut.conjNormal b
    have hσapp : ∀ y : ↥N, ((σ y : ↥N) : G) = b * (y : G) * b⁻¹ := fun y => rfl
    have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    have hσσ : σ * σ = 1 := MulEquiv.ext fun y => Subtype.ext (by
      change b * (b * (y : G) * b⁻¹) * b⁻¹ = y
      rw [hbi, ← mul_assoc, ← mul_assoc, hbb, one_mul, mul_assoc, hbb, mul_one])
    have hσout : σ ∉ inner ↥N := by
      rintro ⟨n, hn⟩
      apply hbN
      have hmem : (n : G)⁻¹ * b ∈ centralizer (N : Set G) := by
        rw [mem_centralizer_iff]
        intro x hx
        have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : G)) hn
        change (n : G) * x * (n : G)⁻¹ = b * x * b⁻¹ at h2
        calc x * ((n : G)⁻¹ * b) = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * b := by group
          _ = (n : G)⁻¹ * (b * x * b⁻¹) * b := by rw [h2]
          _ = ((n : G)⁻¹ * b) * x := by group
      rw [hC, mem_bot, inv_mul_eq_one] at hmem
      rw [← hmem]
      exact n.2
    have hY : (Sporadic.Schreier.fixSub σ).map N.subtype = centralizer ({b} : Set G) ⊓ N := by
      ext x
      simp only [mem_map, mem_inf, subtype_apply, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h1 : σ y = y := hy
        have h2 := congrArg Subtype.val h1
        rw [hσapp] at h2
        refine ⟨?_, y.2⟩
        calc (y : G) * b = b * (y : G) * b⁻¹ * b := by rw [h2]
          _ = b * (y : G) := by group
      · rintro ⟨hx, hxN⟩
        refine ⟨⟨x, hxN⟩, ?_, rfl⟩
        show σ ⟨x, hxN⟩ = ⟨x, hxN⟩
        apply Subtype.ext
        rw [hσapp]
        change b * x * b⁻¹ = x
        rw [← hx, mul_inv_cancel_right]
    obtain ⟨hle, hP⟩ := isPComponent_of_map_eq hKN hKb hKc hY
    obtain ⟨hcomp, hcard⟩ := isComponent_of_equiv (B := (K.subgroupOf N).subgroupOf _)
      hP.choose_spec.2.1 (((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hKN)).trans eK)
      hQc
    rcases hSuzO ↥N ⟨ψ⟩ σ hσσ hσout _ hcomp with h1 | h1 <;> omega

end CFSG.ComponentClassification.GSThmB.X11
