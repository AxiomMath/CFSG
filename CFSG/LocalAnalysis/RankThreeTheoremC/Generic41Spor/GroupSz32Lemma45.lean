module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate9530
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32Loc
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupWitness
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupCyclic25Compl
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSzCore
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

theorem sz32_exists_outside_fixed {R Ω : Type} [Group R] [Finite R] [MulAction R Ω] [Finite Ω]
    (S : Subgroup R) (hR : Nat.card R = 125) (hΩ : Nat.card Ω = 1025)
    (hfree : ∀ s ∈ S, s ≠ 1 → ∀ ω : Ω, s • ω ≠ ω) :
    ∃ g : R, g ∉ S ∧ ∃ ω : Ω, g • ω = ω := by
  classical
  by_contra hcon
  push Not at hcon
  haveI := Fintype.ofFinite R
  haveI := Fintype.ofFinite Ω
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group R Ω
  have hz : ∀ g : R, g ≠ 1 → Fintype.card (MulAction.fixedBy Ω g) = 0 := by
    intro g hg
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨ω, hω⟩ => ?_⟩
    by_cases hgS : g ∈ S
    · exact hfree g hgS hg ω (MulAction.mem_fixedBy.1 hω)
    · exact hcon g hgS ω (MulAction.mem_fixedBy.1 hω)
  rw [Finset.sum_eq_single (1 : R) (fun g _ hg => hz g hg) (by simp)] at hb
  have h1 : Fintype.card (MulAction.fixedBy Ω (1 : R)) = Fintype.card Ω := by
    refine Fintype.card_congr (Equiv.subtypeUnivEquiv ?_)
    intro ω
    exact MulAction.mem_fixedBy.2 (one_smul R ω)
  rw [h1, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card (α := R), hΩ, hR] at hb
  omega

theorem sz32_conjNormal_injective {X : Type} [Group X] (K : Subgroup X) [K.Normal]
    (hKc : centralizer (K : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have : x ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro k hk
    have := congrArg (fun a : MulAut K => ((a ⟨k, hk⟩ : K) : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc k * x = (x * k * x⁻¹) * x := by rw [this]
      _ = x * k := by group
  rw [hKc] at this
  exact Subgroup.mem_bot.mp this

theorem sz32_map_conjNormal_eq_inner {X : Type} [Group X] (K : Subgroup X) [K.Normal] :
    K.map (MulAut.conjNormal : X →* MulAut K) = inner K := by
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, by rw [← MulAut.conjNormal_val]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(k : X), k.2, MulAut.conjNormal_val⟩

theorem sz32_index_dvd_card_outer {X : Type} [Group X] (K : Subgroup X) [K.Normal]
    (hKc : centralizer (K : Set X) = ⊥) : K.index ∣ Nat.card (Outer K) := by
  have h := Subgroup.index_map_of_injective (H := K) (f := (MulAut.conjNormal : X →* MulAut K))
    (sz32_conjNormal_injective K hKc)
  rw [sz32_map_conjNormal_eq_inner] at h
  exact ⟨_, h⟩

theorem sz32_index_eq_five {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hKc : centralizer (K : Set X) = ⊥) (hK : IsSz32Type 5 ↥K)
    {u : X} (huK : u ∉ K) : K.index = 5 := by
  have h1 : K.index ∣ 5 :=
    (sz32_index_dvd_card_outer K hKc).trans (dvd_of_eq (sz32_outer K hK))
  have h2 : K.index ≠ 1 := by
    intro h
    exact huK ((Subgroup.index_eq_one.1 h) ▸ Subgroup.mem_top u)
  exact ((Nat.dvd_prime Nat.prime_five).1 h1).resolve_left h2

theorem sz32_factorization_five : (162688000 : ℕ).factorization 5 = 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : (162688000 : ℕ) = 5 ^ 3 * (2 ^ 10 * 31 * 41) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_pow (by norm_num)]
  have : ¬ 5 ∣ 2 ^ 10 * 31 * 41 := by norm_num
  rw [Nat.factorization_eq_zero_of_not_dvd this]
  simp

theorem sz32_card_K {K : Type} [Group K]
    (hK : IsSz32Type 5 K) : Nat.card K = 32537600 :=
  (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hK.2).card

theorem sz32_card_sylow5 {X : Type}
    [Group X] [Finite X] (K : Subgroup X) (hK : IsSz32Type 5 ↥K) (hidx : K.index = 5)
    (R : Sylow 5 X) : Nat.card (R : Subgroup X) = 125 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h1 := Subgroup.card_mul_index K
  rw [sz32_card_K hK, hidx] at h1
  rw [Sylow.card_eq_multiplicity, ← h1]
  have h2 : (32537600 * 5 : ℕ) = 162688000 := by norm_num
  rw [h2, sz32_factorization_five]
  norm_num

theorem sz32_inf_card_cyclic {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hK : IsSz32Type 5 ↥K) (R : Sylow 5 X) :
    Nat.card (((R : Subgroup X) ⊓ K : Subgroup X)) = 25 ∧
      IsCyclic (((R : Subgroup X) ⊓ K : Subgroup X)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := exists_sylow_inf_normal K R
  obtain ⟨hcyc, hcard⟩ := sz32_sylow K hK P
  rw [← hP]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hcard]
    norm_num
  · haveI := hcyc
    exact isCyclic_of_surjective (K.subtype.subgroupMap (P : Subgroup K))
      (K.subtype.subgroupMap_surjective _)

theorem sz32_subgroupOf_card_cyclic {X : Type} [Group X] [Finite X]
    (K : Subgroup X) [K.Normal] (hK : IsSz32Type 5 ↥K) (R : Sylow 5 X) :
    Nat.card (K.subgroupOf (R : Subgroup X)) = 25 ∧ IsCyclic (K.subgroupOf (R : Subgroup X)) := by
  have heq : K.subgroupOf (R : Subgroup X) =
      ((R : Subgroup X) ⊓ K).subgroupOf (R : Subgroup X) := by
    rw [inf_comm, Subgroup.inf_subgroupOf_right]
  obtain ⟨hcard, hcyc⟩ := sz32_inf_card_cyclic K hK R
  rw [heq]
  refine ⟨?_, ?_⟩
  · rw [← hcard]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : (R : Subgroup X) ⊓ K ≤ R)).toEquiv
  · haveI := hcyc
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : (R : Subgroup X) ⊓ K ≤ R)).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : (R : Subgroup X) ⊓ K ≤ R)).symm.surjective

theorem sz32_subgroupOf_index
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (hK : IsSz32Type 5 ↥K)
    (hidx : K.index = 5) (R : Sylow 5 X) : (K.subgroupOf (R : Subgroup X)).index = 5 := by
  have h1 : Nat.card (K.subgroupOf (R : Subgroup X)) = 25 :=
    (sz32_subgroupOf_card_cyclic K hK R).1
  have h2 := Subgroup.card_mul_index (K.subgroupOf (R : Subgroup X))
  rw [h1, sz32_card_sylow5 K hK hidx R] at h2
  omega

theorem sz32_isSimpleGroup {K : Type} [Group K]
    (hK : IsSz32Type 5 K) : IsSimpleGroup K := by
  obtain ⟨-, hiso⟩ := hK
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
  exact eF.isSimpleGroup

theorem sz32_free_on_sylow2 {X : Type}
    [Group X] [Finite X] (K : Subgroup X) [K.Normal] (hK : IsSz32Type 5 ↥K) (R : Sylow 5 X)
    {s : X} (hsR : s ∈ (R : Subgroup X)) (hsK : s ∈ K) (hs1 : s ≠ 1) (V : Sylow 2 K) :
    (MulAut.conjNormal s : MulAut K) • V ≠ V := by
  intro hfix
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hK.2
  have hmem : s ∈ (R : Subgroup X) ⊓ K := ⟨hsR, hsK⟩
  have hdvd : orderOf s ∣ 25 := by
    have := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [(sz32_inf_card_cyclic K hK R).1] at this
  have hord : orderOf (⟨s, hsK⟩ : K) ∣ 25 := by
    rw [← Subgroup.orderOf_coe]
    exact hdvd
  have hcop : Nat.Coprime (orderOf (⟨s, hsK⟩ : K)) 31744 :=
    Nat.Coprime.coprime_dvd_left hord (by norm_num)
  have h1 : (⟨s, hsK⟩ : K) • V = V := by
    have : (MulAut.conjNormal s : MulAut K) = MulAut.conj (⟨s, hsK⟩ : K) :=
      MulAut.conjNormal_val (h := ⟨s, hsK⟩)
    rw [Sylow.smul_def, ← this]
    exact hfix
  have h2 := CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.eq_one_of_smul_eq hSz hcop h1
  exact hs1 (congrArg Subtype.val h2)

theorem sz32_exists_fixed_outer
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (hK : IsSz32Type 5 ↥K)
    (hidx : K.index = 5) (R : Sylow 5 X) :
    ∃ g : ↥(R : Subgroup X), g ∉ K.subgroupOf (R : Subgroup X) ∧ g ^ 5 = 1 ∧
      ∃ ω : Sylow 2 K, (MulAut.conjNormal (g : X) : MulAut K) • ω = ω := by
  classical
  let R₀ : Subgroup X := (R : Subgroup X)
  letI : MulAction ↥R₀ (Sylow 2 K) :=
    MulAction.compHom _ ((MulAut.conjNormal : X →* MulAut K).comp R₀.subtype)
  have hcardR : Nat.card R₀ = 125 := sz32_card_sylow5 K hK hidx R
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hK.2
  have hfree : ∀ s ∈ K.subgroupOf R₀, s ≠ 1 → ∀ ω : Sylow 2 K, s • ω ≠ ω := by
    intro s hs hs1 ω
    exact sz32_free_on_sylow2 K hK R s.2 hs (fun h => hs1 (Subtype.ext h)) ω
  obtain ⟨g, hgS, ω, hω⟩ :=
    sz32_exists_outside_fixed (K.subgroupOf R₀) hcardR hSz.card_sylow hfree
  have hg5S : g ^ 5 ∈ K.subgroupOf R₀ := by
    have := Subgroup.pow_index_mem (K.subgroupOf R₀) g
    rwa [sz32_subgroupOf_index K hK hidx R] at this
  have hfix5 : (g ^ 5) • ω = ω := by
    have : g ^ 5 ∈ MulAction.stabilizer ↥R₀ ω :=
      (MulAction.stabilizer ↥R₀ ω).pow_mem (MulAction.mem_stabilizer_iff.2 hω) 5
    exact MulAction.mem_stabilizer_iff.1 this
  have hg5 : g ^ 5 = 1 := by
    by_contra h
    exact hfree _ hg5S h ω hfix5
  exact ⟨g, hgS, hg5, ω, hω⟩

theorem sz32_mem_iff_of_smul_eq {K : Type} [Group K] {a : MulAut K} {V : Sylow 2 K}
    (h : a • V = V) (k : K) : a k ∈ (V : Subgroup K) ↔ k ∈ (V : Subgroup K) := by
  have h' : a • (V : Subgroup K) = (V : Subgroup K) := by
    rw [← Sylow.pointwise_smul_def, h]
  have h2 : a • k ∈ a • (V : Subgroup K) ↔ k ∈ (V : Subgroup K) :=
    Subgroup.smul_mem_pointwise_smul_iff
  rw [h'] at h2
  exact h2

theorem sz32_mem_normalizer_map_subtype {X : Type} [Group X] (K : Subgroup X) [K.Normal]
    {V₀ : Subgroup K} {x : X}
    (hV : ∀ k : K, (MulAut.conjNormal x : MulAut K) k ∈ V₀ ↔ k ∈ V₀) :
    x ∈ normalizer ((V₀.map K.subtype : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨MulAut.conjNormal x k, (hV k).2 hk, by simp [MulAut.conjNormal_apply]⟩
  · rintro ⟨k', hk', hk'h⟩
    refine ⟨(MulAut.conjNormal x)⁻¹ k', (hV _).1 (by simpa using hk'), ?_⟩
    rw [Subgroup.coe_subtype, MulAut.conjNormal_inv_apply]
    have : (k' : X) = x * h * x⁻¹ := hk'h
    rw [this]
    group

theorem sz32_outer_acts_nontrivially
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (hKc : centralizer (K : Set X) = ⊥) (hK : IsSz32Type 5 ↥K) (R : Sylow 5 X) {u : X}
    (huR : u ∈ (R : Subgroup X)) (huK : u ∉ K) :
    ∃ s ∈ K.subgroupOf (R : Subgroup X),
      (⟨u, huR⟩ : (R : Subgroup X)) * s * (⟨u, huR⟩ : (R : Subgroup X))⁻¹ ≠ s := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := exists_sylow_inf_normal K R
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hK.2
  have hsimple := sz32_isSimpleGroup hK
  have hOut : (inner K).index ∣ 5 := dvd_of_eq (sz32_outer K hK)
  have hf : ∀ x ∈ (P : Subgroup K), (MulAut.conjNormal u : MulAut K) x = x := by
    intro x hx
    have hxRK : (x : X) ∈ (R : Subgroup X) ⊓ K := by
      rw [← hP]
      exact ⟨x, hx, rfl⟩
    have h1 := hcon ⟨(x : X), hxRK.1⟩
      (show (⟨(x : X), hxRK.1⟩ : (R : Subgroup X)) ∈ K.subgroupOf (R : Subgroup X) from hxRK.2)
    have h2 := congrArg Subtype.val h1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    simpa using h2
  obtain ⟨t, htP, hft⟩ := (sz32_data K hK P).aut hSz hsimple hOut hf
  have : u = (t : X) := by
    apply sz32_conjNormal_injective K hKc
    rw [hft]
    exact MulAut.conjNormal_val.symm
  exact huK (this ▸ t.2)

theorem sz32_sylow_eq_inf_mul_pow
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (hK : IsSz32Type 5 ↥K)
    (hidx : K.index = 5) (R : Sylow 5 X) {u : X} (huR : u ∈ (R : Subgroup X)) (huK : u ∉ K)
    (r : (R : Subgroup X)) :
    ∃ s ∈ K.subgroupOf (R : Subgroup X), ∃ i : ℕ,
      r = s * (⟨u, huR⟩ : (R : Subgroup X)) ^ i := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQ : Nat.card ((R : Subgroup X) ⧸ K.subgroupOf (R : Subgroup X)) = 5 :=
    sz32_subgroupOf_index K hK hidx R
  have hq1 : (QuotientGroup.mk (⟨u, huR⟩ : (R : Subgroup X)) :
      (R : Subgroup X) ⧸ K.subgroupOf (R : Subgroup X)) ≠ 1 := fun h =>
    huK ((QuotientGroup.eq_one_iff (⟨u, huR⟩ : (R : Subgroup X))).1 h)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_of_prime_card hQ hq1
      (g' := (QuotientGroup.mk r : (R : Subgroup X) ⧸ K.subgroupOf (R : Subgroup X))))
  refine ⟨r * ((⟨u, huR⟩ : (R : Subgroup X)) ^ k)⁻¹, ?_, k, by group⟩
  rw [← QuotientGroup.ker_mk' (K.subgroupOf (R : Subgroup X)), MonoidHom.mem_ker]
  have : (QuotientGroup.mk' (K.subgroupOf (R : Subgroup X))) (⟨u, huR⟩ : (R : Subgroup X)) ^ k =
      (QuotientGroup.mk' (K.subgroupOf (R : Subgroup X))) r := hk
  rw [map_mul, map_inv, map_pow, this, mul_inv_cancel]

theorem sz32_lemma45 :
    Lemma45Facts IsSz32Type 5 Sz32Shape := by
  classical
  intro X _ _ K hK R U₀ hUR _ hUc hshape
  obtain ⟨hKn, hKc, hKT⟩ := hK
  haveI : K.Normal := hKn
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, huU, huK⟩ := SetLike.not_le_iff_exists.1 hshape
  have hu1 : u ≠ 1 := fun h => huK (h ▸ K.one_mem)
  have hU : U₀ = zpowers u := eq_zpowers_of_card_prime Nat.prime_five hUc huU hu1
  have hord : orderOf u = 5 := by rw [← Nat.card_zpowers, ← hU, hUc]
  have hu5 : u ^ 5 = 1 := by rw [← hord]; exact pow_orderOf_eq_one u
  have huR : u ∈ (R : Subgroup X) := hUR huU
  have hidx : K.index = 5 := sz32_index_eq_five K hKc hKT huK
  obtain ⟨hScard, hScyc⟩ := sz32_subgroupOf_card_cyclic K hKT R
  let R₀ : Subgroup X := (R : Subgroup X)
  let S : Subgroup R₀ := K.subgroupOf R₀
  have hSn : S.Normal := inferInstance
  let u₀ : R₀ := ⟨u, huR⟩
  have hu₀5 : u₀ ^ 5 = 1 := Subtype.ext (by simpa using hu5)
  have hnt : ∃ s ∈ S, u₀ * s * u₀⁻¹ ≠ s := sz32_outer_acts_nontrivially K hKc hKT R huR huK
  have hR : ∀ r : R₀, ∃ s ∈ S, ∃ i : ℕ, r = s * u₀ ^ i :=
    sz32_sylow_eq_inf_mul_pow K hKT hidx R huR huK
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hKT.2
  obtain ⟨g, hgS, hg5, ω, hω⟩ := sz32_exists_fixed_outer K hKT hidx R
  obtain ⟨s, hsS, j, hj0, hj5, hsg⟩ :=
    complement_conj_of_cyclic25 S hScard hScyc hSn hu₀5 hnt hR hg5 hgS
  let a : MulAut K := MulAut.conjNormal (s : X)
  have hsgX : (s : X) * (g : X) * (s : X)⁻¹ = u ^ j := by
    have := congrArg Subtype.val hsg
    simpa [u₀] using this
  have hfixj : (MulAut.conjNormal (u ^ j) : MulAut K) • (a • ω) = a • ω := by
    rw [← hsgX, map_mul, map_mul, map_inv, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one,
      mul_smul, hω]
  have hfixu : (MulAut.conjNormal u : MulAut K) • (a • ω) = a • ω := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, u = (u ^ j) ^ m := by
      interval_cases j
      · exact ⟨1, by simp⟩
      · exact ⟨3, by rw [← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_add, hu5]; simp⟩
      · exact ⟨2, by rw [← pow_mul, show 3 * 2 = 5 + 1 by norm_num, pow_add, hu5]; simp⟩
      · exact ⟨4, by
          rw [← pow_mul, show 4 * 4 = 5 * 3 + 1 by norm_num, pow_add, pow_mul, hu5]; simp⟩
    have hmem : (MulAut.conjNormal (u ^ j) : MulAut K) ∈
        MulAction.stabilizer (MulAut K) (a • ω) := hfixj
    have := (MulAction.stabilizer (MulAut K) (a • ω)).pow_mem hmem m
    rw [← map_pow, ← hm] at this
    exact this
  refine ⟨((a • ω : Sylow 2 K) : Subgroup K).map K.subtype, Subgroup.map_subtype_le _,
    (a • ω : Sylow 2 K).isPGroup'.map K.subtype, ?_, ?_⟩
  ·
    rw [hU, Subgroup.zpowers_le]
    exact sz32_mem_normalizer_map_subtype K (fun k => sz32_mem_iff_of_smul_eq hfixu k)
  ·
    intro hVN
    obtain ⟨P, hP⟩ := exists_sylow_inf_normal K R
    have hmemP : ∀ q : K, q ∈ (P : Subgroup K) ↔ (q : X) ∈ (R : Subgroup X) ⊓ K := by
      intro q
      rw [← hP]
      constructor
      · intro hq
        exact ⟨q, hq, rfl⟩
      · rintro ⟨q', hq', hq'q⟩
        have : q' = q := Subtype.ext hq'q
        rw [← this]
        exact hq'
    have hle : ((a • ω : Sylow 2 K) : Subgroup K) ≤ normalizer ((P : Subgroup K) : Set K) := by
      intro v hv
      rw [Subgroup.mem_normalizer_iff]
      intro p
      have hvN : (v : X) ∈ normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
        hVN ⟨v, hv, rfl⟩
      rw [hmemP, hmemP]
      have := Subgroup.mem_normalizer_iff.1 hvN (p : X)
      simpa using this
    have h1 := Subgroup.card_le_of_le hle
    rw [CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.card_two hSz (a • ω),
      (sz32_data K hKT P).card_normalizer] at h1
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
