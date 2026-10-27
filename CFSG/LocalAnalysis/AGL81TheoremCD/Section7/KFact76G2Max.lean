module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Model
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate120
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Minus
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Plus
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2LongRoot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76SL3Sylow
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2Minus
import CFSG.RankThree.PartTwo.Sec12.Hering129LG2
import CFSG.RankThree.PartTwo.Sec12.Hering129KRes
import CFSG.RankThree.PartTwo.Sec12.Hering129HBasic
import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.BridgeOdd
import CFSG.Quasithin.H13.ModelsG2
import CFSG.LieType.Chevalley.Braid
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
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
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.RankThree.PartOne.D4RC.RxIso
import CFSG.RankThree.PartOne.SEITZ7.D4Final
import CFSG.RankThree.PartTwo.KFacts.K412Alternating
import CFSG.RankThree.PartTwo.KFacts.KS12OrderNineProof
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
import CFSG.RankThree.PartTwo.Sec12.Hering129GCore
import CFSG.RankThree.PartTwo.Sec12.Hering129GHJBranch
import CFSG.RankThree.PartTwo.Sec12.Hering129GMod9
import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd
import CFSG.RankThree.PartTwo.Sec12.Hering129HNot9
import CFSG.RankThree.PartTwo.Sec12.Hering129KModels
import CFSG.RankThree.PartTwo.Sec12.Hering129List
import CFSG.RankThree.PartTwo.Sec12.Item12ResProofFree
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Frame
import CFSG.RankThree.PartTwo.Sec13.Item131Assembly
import CFSG.RankThree.PartTwo.Sec13.Item131bProofK
import CFSG.RankThree.PartTwo.Sec13.Item131bProofOmega
import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTwelve
import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTwo
import CFSG.RankThree.PartTwo.Sec21.Item2113ProofU4
import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlockMain
import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data
import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofAssembly
import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofPairing
import Certificates.Certificate17002
import Certificates.Certificate17951

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport G2Max CFSG.RankThree.PartTwo

private theorem mem_normalizer_zpowers_of_conj {G : Type*} [Group G] {n z : G} {k : ℤ}
    (h : n * z * n⁻¹ = z ^ k) (h' : n⁻¹ * z * n = z ^ k) :
    n ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact Subgroup.mem_zpowers_iff.2 ⟨k * m, by rw [← conj_zpow, h, ← zpow_mul]⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine Subgroup.mem_zpowers_iff.2 ⟨k * m, ?_⟩
    calc z ^ (k * m) = (n⁻¹ * z * n⁻¹⁻¹) ^ m := by rw [inv_inv, h', zpow_mul]
      _ = n⁻¹ * (n * g * n⁻¹) * n := by rw [conj_zpow, hm, inv_inv]
      _ = g := by group

private theorem mem_normalizer_zpowers_of_commute {G : Type*} [Group G] {g z : G}
    (h : Commute g z) : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
  mem_normalizer_zpowers_of_conj (k := 1) (by rw [zpow_one, h.eq, mul_inv_cancel_right])
    (by rw [zpow_one, h.inv_left.eq, inv_mul_cancel_right])

private theorem mem_normalizer_zpowers_of_conj_eq_inv {G : Type*} [Group G] {n z : G}
    (h : n * z * n⁻¹ = z⁻¹) : n ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
  mem_normalizer_zpowers_of_conj (k := -1) (by rw [zpow_neg_one, h]) (by
    rw [zpow_neg_one]
    calc n⁻¹ * z * n = n⁻¹ * z⁻¹⁻¹ * n := by rw [inv_inv]
      _ = n⁻¹ * (n * z * n⁻¹)⁻¹ * n := by rw [h]
      _ = z⁻¹ := by group)

private theorem nonempty_centralizer_mulEquiv_conj {G : Type*} [Group G] (n z : G) :
    Nonempty (Subgroup.centralizer ({z} : Set G) ≃*
      Subgroup.centralizer ({n * z * n⁻¹} : Set G)) := by
  have h : (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.centralizer ({n * z * n⁻¹} : Set G) := by
    ext g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
    constructor <;> intro hg
    · calc g * (n * z * n⁻¹) = n * (n⁻¹ * g * n * z) * n⁻¹ := by group
        _ = n * z * n⁻¹ * g := by rw [hg]; group
    · calc n⁻¹ * g * n * z = n⁻¹ * (g * (n * z * n⁻¹)) * n := by group
        _ = z * (n⁻¹ * g * n) := by rw [hg]; group
  exact ⟨((Subgroup.centralizer ({z} : Set G)).equivMapOfInjective (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).trans (MulEquiv.subgroupCongr h)⟩

private theorem eq_top_of_le_map_subtype {G : Type*} [Group G] {S : Subgroup G}
    {M : Subgroup S} (h : S ≤ M.map S.subtype) : M = ⊤ :=
  eq_top_iff.2 fun g _ => by
    obtain ⟨m, hm, hmg⟩ := h g.2
    have hmg' : m = g := Subtype.ext hmg
    rwa [← hmg']

private theorem isCoatom_normalizer_zpowers {G : Type} [Group G] [IsSimpleGroup G] {q : ℕ}
    (hq : 2 < q) {z t : G} (hSL : Sec4.IsSLThreePiAt (Subgroup.centralizer ({z} : Set G)) q)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (ht3 : t ^ 3 ≠ 1) (hcz : Commute t z)
    (hover : ∀ M : Subgroup G, Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤ M →
      ∀ x ∈ M, ¬ Commute (x * t * x⁻¹) t → ¬ Commute (x * t * x⁻¹) z → M = ⊤) :
    IsCoatom (Subgroup.normalizer (Subgroup.zpowers z : Set G)) := by
  have htZ : t ∉ Subgroup.zpowers z := fun ht => ht3 (by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ht
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow])
  refine ⟨fun htop => ?_, fun M hM => ?_⟩
  · have := Subgroup.normalizer_eq_top_iff.1 htop
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.zpowers z) with h | h
    · exact hz1 (Subgroup.zpowers_eq_bot.1 h)
    · exact htZ (by rw [h]; exact Subgroup.mem_top t)
  · obtain ⟨x, hxM, h1, h2⟩ := exists_conj_not_commute_of_normalizer_lt
      (Sec12.Hering129KRes.isQuasisimple_of_isSLThreePiAt hSL hq)
      (exists_sylow_three_center_le_of_isSLThreePiAt hSL).2 hcz htZ hM
    exact hover M hM.le x hxM h1 h2

private theorem three_ne_zero_of_ringChar_ne {K : Type} [Field K] (hK3 : ringChar K ≠ 3) :
    (3 : K) ≠ 0 := fun h => ((Nat.dvd_prime Nat.prime_three).1
  ((ringChar.spec K 3).1 (by exact_mod_cast h))).elim CharP.ringChar_ne_one hK3


section Model

variable {K : Type} [Field K] [Finite K]

local notation "X" => pinnedX Tag.G2 K

private theorem isSLThreePiAt_centralizer (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hzR : (z : ModGL .G2 K) ∈ Subgroup.closure (Set.range (X gR) ∪ Set.range (X (-gR)))) :
    Sec4.IsSLThreePiAt (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) (Nat.card K) := by
  obtain ⟨n, hn⟩ : ∃ n : adjointGroup .G2 K,
      (n : ModGL .G2 K) = weylElt .G2 K iR 1 * weylElt .G2 K iA 1 :=
    ⟨⟨_, mul_mem (weylElt_mem_adjointGroup _ _) (weylElt_mem_adjointGroup _ _)⟩, rfl⟩
  have hS : n * z * n⁻¹ ∈ Sec11.KS11Lie4Proof.g2ShortSL2 K := by
    rw [Subgroup.closure_union] at hzR
    have h1 := weyl_range_step (γ := gU) iA isRoot_gR (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl) _ hzR
    have h2 := weyl_range_step (γ := gV) iR isRoot_gU (by funext i; fin_cases i <;> rfl)
      (by funext i; fin_cases i <;> rfl) _ h1
    show (n : ModGL .G2 K) * z * (n : ModGL .G2 K)⁻¹ ∈
      rootSubgroup .G2 K gV ⊔ rootSubgroup .G2 K (-gV)
    rw [hn, show weylElt .G2 K iR 1 * weylElt .G2 K iA 1 * (z : ModGL .G2 K) *
        (weylElt .G2 K iR 1 * weylElt .G2 K iA 1)⁻¹ = weylElt .G2 K iR 1 *
        (weylElt .G2 K iA 1 * z * (weylElt .G2 K iA 1)⁻¹) * (weylElt .G2 K iR 1)⁻¹ by group]
    exact h2
  obtain ⟨-, hSL⟩ := Sec12.Hering129L.g2_centralizer_threeA hK3 hK4 hS
    (by rw [conj_pow, hz3, mul_one, mul_inv_cancel]) fun h => hz1 (conj_eq_one_iff.1 h)
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_conj n z
  exact Sec12.isSLThreePiAt_congr e.symm hSL

private theorem exists_isCoatom_of_overgroup (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hzR : (z : ModGL .G2 K) ∈ Subgroup.closure (Set.range (X gR) ∪ Set.range (X (-gR))))
    (hcz : Commute (X gC 1) z)
    (hover : ∀ H : Subgroup (ModGL .G2 K), (∀ g ∈ adjointGroup .G2 K, Commute g z → g ∈ H) →
      (∀ g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set (adjointGroup .G2 K)),
        (g : ModGL .G2 K) ∈ H) →
      ∀ x ∈ adjointGroup .G2 K, x ∈ H → ¬ Commute (x * X gC 1 * x⁻¹) (X gC 1) →
        ¬ Commute (x * X gC 1 * x⁻¹) z → adjointGroup .G2 K ≤ H) :
    ∃ z : adjointGroup .G2 K, z ^ 3 = 1 ∧ z ≠ 1 ∧
      Sec4.IsSLThreePiAt (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) (Nat.card K) ∧
      IsCoatom (Subgroup.normalizer (Subgroup.zpowers z : Set (adjointGroup .G2 K))) := by
  have := CFSG.Quasithin.H13.isSimpleGroup_adjointGroup_G2 (K := K) (by omega)
  have hSL := isSLThreePiAt_centralizer hK3 hK4 hz3 hz1 hzR
  have ht3 : (⟨X gC 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .G2 K) ^ 3 ≠ 1 := fun h => by
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
    exact one_ne_zero (pinnedX_injective .G2 K gC ((Z_no_three_torsion
      (three_ne_zero_of_ringChar_ne hK3) _ (X_mem_Zg 1) h').trans (pinnedX_zero .G2 K gC).symm))
  refine ⟨z, hz3, hz1, hSL, isCoatom_normalizer_zpowers (by omega) hSL hz3 hz1 ht3
    (Subtype.ext hcz) fun M hM x hxM h1 h2 => eq_top_of_le_map_subtype (hover _
      (fun g hg hgz => ⟨⟨g, hg⟩, hM (mem_normalizer_zpowers_of_commute (Subtype.ext hgz)), rfl⟩)
      (fun g hg => ⟨g, hM hg, rfl⟩) x x.2 ⟨x, hxM, rfl⟩ (fun h => h1 (Subtype.ext h))
      fun h => h2 (Subtype.ext h))⟩

private theorem exists_isCoatom_normalizer (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) :
    ∃ z : adjointGroup .G2 K, z ^ 3 = 1 ∧ z ≠ 1 ∧
      Sec4.IsSLThreePiAt (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) (Nat.card K) ∧
      IsCoatom (Subgroup.normalizer (Subgroup.zpowers z : Set (adjointGroup .G2 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := three_ne_zero_of_ringChar_ne hK3
  rcases Sec11.KS11Lie4Proof.three_dvd_card_sub_one_or_add_one hK3 with hq | hq
  ·
    obtain ⟨ω, hord⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
      (by rw [Nat.card_units]; exact hq)
    have hω3 : ω ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
    have hω1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hord; omega
    have hω : (ω : K) ^ 2 + ω + 1 = 0 := by
      have h1 : (ω : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hω1 (Units.val_eq_one.1 h)
      have h3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
      exact (mul_eq_zero.1 (by linear_combination h3' :
        ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0)).resolve_left h1
    obtain ⟨z, hz⟩ : ∃ z : adjointGroup .G2 K, (z : ModGL .G2 K) = torusElt .G2 K iR ω :=
      ⟨⟨_, torusElt_mem_adjointGroup _ _⟩, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n : adjointGroup .G2 K, (n : ModGL .G2 K) = weylElt .G2 K iR 1 :=
      ⟨⟨_, weylElt_mem_adjointGroup _ _⟩, rfl⟩
    have hnN := mem_normalizer_zpowers_of_conj_eq_inv (n := n) (z := z) (Subtype.ext (show
        (n : ModGL .G2 K) * z * (n : ModGL .G2 K)⁻¹ = (z : ModGL .G2 K)⁻¹ by
      rw [hn, hz, weylElt_one_mul_torusElt_mul_inv .G2 K iR iR ω]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← torusElt_mul, ← torusElt_mul, show Tag.G2.cartan iR iR = 2 by decide,
        show ω * ω ^ (-(2 : ℤ)) * ω = 1 by group, torusElt_one]))
    refine exists_isCoatom_of_overgroup (z := z) hK3 hK4 (Subtype.ext (by
      rw [Subgroup.coe_pow, hz, pow_three, ← torusElt_mul, ← torusElt_mul, ← pow_three, hω3,
        torusElt_one, Subgroup.coe_one]))
      (fun h => hω1 ?_) (by rw [hz]; exact torusElt_iR_mem ω) ?_
      fun H hC hN x hx hxH h1 h2 => adjointGroup_le_of_overgroup_torus h3 hω
        (fun g hg hgz => hC g hg (by rwa [hz])) (by rw [← hn]; exact hN n hnN) hx hxH h1
        (by rwa [← hz])
    ·
      have e := root_torus_conjugation iR isRoot_gV ω (1 : K)
      rw [← hz, show (z : ModGL .G2 K) = 1 from congrArg Subtype.val h,
        show ∑ j, Tag.G2.cartan iR j * gV j = 1 by decide, zpow_one] at e
      simp only [one_mul, inv_one, mul_one] at e
      exact Units.val_eq_one.1 (pinnedX_injective .G2 K gV e).symm
    ·
      have e := root_torus_conjugation iR isRoot_gC ω (1 : K)
      rw [show ∑ j, Tag.G2.cartan iR j * gC j = 0 by decide, zpow_zero, Units.val_one,
        one_mul] at e
      rw [hz]
      exact (mul_inv_eq_iff_eq_mul.1 e).symm
  ·
    have hK := CFSG.HardMathSupport.Seitz.Proving.no_root_of_three_dvd hq
    obtain ⟨z, hz⟩ : ∃ z : adjointGroup .G2 K, (z : ModGL .G2 K) = zr K :=
      ⟨⟨_, zr_mem_adjointGroup⟩, rfl⟩
    exact exists_isCoatom_of_overgroup (z := z) hK3 hK4
      (Subtype.ext (by rw [Subgroup.coe_pow, hz, zr_pow_three, Subgroup.coe_one]))
      (fun h => orderThreeSL_ne_one (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
        (τ := .G2) (K := K) gR (by
          rw [map_one, ← zr_eq_rootSL2, ← hz]
          exact congrArg Subtype.val h)))
      (by rw [hz]; exact zr_mem) (by rw [hz]; exact commute_pinnedX_c_zr 1)
      fun H hC _ x hx hxH h1 h2 => adjointGroup_le_of_overgroup_zr hK
        (exists_ne_zero_ne_one (by omega)) (fun g hg hgz => hC g hg (by rwa [hz])) hx hxH h1
        (by rwa [← hz])

end Model

theorem g2ModelNormalizerMax_holds : G2ModelNormalizerMax := by
  intro K _ _ hK3 hK4 A hA hwc
  obtain ⟨z, hz3, hz1, hSL, hco⟩ := exists_isCoatom_normalizer hK3 hK4
  obtain ⟨g, hg⟩ := exists_conj_eq_zpowers_of_isSLThreePiAt hA hwc hz3 hz1 hSL
  rw [← hg] at hco
  refine (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) _).1 ?_
  rw [MulEquiv.coe_mapSubgroup, Subgroup.map_equiv_normalizer_eq]
  exact hco

theorem kFactG2NormalizerMax_holds : KFactG2NormalizerMax :=
  kFactG2NormalizerMax_of_model g2ModelNormalizerMax_holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
