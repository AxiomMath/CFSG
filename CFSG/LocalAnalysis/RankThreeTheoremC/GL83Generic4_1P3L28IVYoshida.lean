module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVQStruct
public import CFSG.GH74.GLS.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVPsi
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVQP
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVWreath
import CFSG.RankThree.Transfer.Yoshida
import CFSG.RankThree.PartTwo.Sec8.Transfer
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlaneLines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Basics
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.Quasithin.Background.F6CatRecogOut
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1End
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l28iv_mem_plane_of_pow_three {T Z : Subgroup G} {t₀ x : G} (hT : T = zpowers t₀)
    (ht₀ : orderOf t₀ = 9) (hZc : IsCyclic ↥Z) (hxZ : x ∈ Z) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hTZ : T ⊓ Z = ⊥) (hcomm : ∀ a ∈ T, ∀ c ∈ Z, a * c = c * a) {e : G} (he : e ∈ T ⊔ Z)
    (he3 : e ^ 3 = 1) : e ∈ zpowers (t₀ ^ 3) ⊔ zpowers x := by
  obtain ⟨a, haT, c, hcZ, rfl⟩ := u3l42_decomp hcomm he
  have hac3 : a ^ 3 = 1 ∧ c ^ 3 = 1 := by
    have h1 : a ^ 3 * c ^ 3 = 1 := by
      rw [← (Commute.mul_pow (show Commute a c from hcomm a haT c hcZ) 3), he3]
    have h2 : a ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : a ^ 3 ∈ T ⊓ Z := Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ haT 3, by
      rw [h2]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcZ 3)⟩
    rw [hTZ, mem_bot] at h3
    refine ⟨h3, ?_⟩
    rw [h3] at h2
    exact inv_eq_one.mp h2.symm
  have hcx : c ∈ zpowers x := mem_zpowers_of_isCyclic_of_pow_three hZc hxZ hcZ hx1 hx3 hac3.2
  have h9 : t₀ ^ 9 = 1 := by rw [← ht₀]; exact pow_orderOf_eq_one t₀
  have huT : t₀ ^ 3 ∈ T := by rw [hT]; exact pow_mem (mem_zpowers t₀) 3
  have hu3 : (t₀ ^ 3) ^ 3 = 1 := by rw [← pow_mul, show 3 * 3 = 9 from rfl, h9]
  have hu1 : t₀ ^ 3 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) h
    omega
  have hTcyc : IsCyclic ↥T := by rw [hT]; infer_instance
  have hau : a ∈ zpowers (t₀ ^ 3) :=
    mem_zpowers_of_isCyclic_of_pow_three hTcyc huT haT hu1 hu3 hac3.1
  exact Subgroup.mul_mem _ (mem_sup_left hau) (mem_sup_right hcx)

theorem l28iv_exists_outside (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J) :
    ∃ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ 3 = 1 ∧
      y ∉ ((P : Subgroup G) ⊓ J) ⊔ l28ivZ P x J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, hxLO, -, hrk⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨-, hxZ, hTZ, hcomm, hZc⟩ := l28iv_Z_facts hS hU0 hK1 hp hM hgen hJ
  obtain ⟨t₀, hT, ht₀⟩ := l28iv_T_cyclic hS hU0 hK1 hp hM hgen hJ
  obtain ⟨E, hEQ, hEel, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
    Nat.prime_three ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
  rw [hrk] at hEc
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  by_contra hno
  push Not at hno
  have hE : E ≤ zpowers (t₀ ^ 3) ⊔ zpowers x := fun e he =>
    l28iv_mem_plane_of_pow_three hT ht₀ hZc hxZ hx1 hx3 hTZ hcomm
      (hno e (hEQ he) (hEel.2 e he)) (hEel.2 e he)
  have h9 : t₀ ^ 9 = 1 := by rw [← ht₀]; exact pow_orderOf_eq_one t₀
  have huT : t₀ ^ 3 ∈ (P : Subgroup G) ⊓ J := by rw [hT]; exact pow_mem (mem_zpowers t₀) 3
  have hu3 : (t₀ ^ 3) ^ 3 = 1 := by rw [← pow_mul, show 3 * 3 = 9 from rfl, h9]
  have hu1 : t₀ ^ 3 ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) h
    omega
  have hxu : x ∉ zpowers (t₀ ^ 3) := fun h => hxJ (zpowers_le.mpr huT.2 h)
  have hux : t₀ ^ 3 * x = x * t₀ ^ 3 := hcomm _ huT x hxZ
  have hplane := (plane_zpowers_sup (x := x) (k := t₀ ^ 3) hx3 hu1 hu3 hxu hux).2
  have h1 := Subgroup.card_le_of_le hE
  rw [hEc, hplane] at h1
  norm_num at h1

theorem l28iv_oResidual_eq_top (hS : Setting G) : CFSG.GH74.GLS.oResidual 3 G = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hS.simple
  obtain ⟨x, hx1, hx⟩ := CFSG.RankThree.PartTwo.Sec8.exists_coprime_orderOf_ne_one hS.nonab 3
  have hN : Subgroup.normalClosure ({x} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({x} : Set G))
      with h | h
    · exact absurd ((Subgroup.mem_bot).mp (h ▸ Subgroup.subset_normalClosure rfl)) hx1
    · exact h
  rw [eq_top_iff, ← hN]
  refine Subgroup.closure_mono fun y hy => ?_
  obtain ⟨z, hz, hzy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  rw [Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨c, hc⟩ := hzy
  show Nat.Coprime (orderOf y) 3
  rw [← SemiconjBy.orderOf_eq (c : G) hc]
  exact hx

theorem l28iv_false_of_wc (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL28Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL28Normal M x J)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) ⊓ centralizer ({x} : Set G) → g * x * g⁻¹ ∈ zpowers x) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, hxLO, -, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hZQ, hxZ, hTZ, hcomm, hZc⟩ := l28iv_Z_facts hS hU0 hK1 hp hM hgen hJ
  obtain ⟨t₀, hT, ht₀⟩ := l28iv_T_cyclic hS hU0 hK1 hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hTdef
  set Z : Subgroup G := l28ivZ P x J with hZdef
  have hx1' : x ∉ zpowers (1 : G) := by
    rw [zpowers_one_eq_bot, mem_bot]
    exact hx1
  have hPC : (P : Subgroup G) ≤ C :=
    l28iv_le_centralizer P.isPGroup' hxP hx3 hx1 hx1' (one_pow 3) fun g hg => Or.inl (hwc g hg)
  have hQP : (P : Subgroup G) ⊓ C = P := inf_eq_left.mpr hPC
  have hNx : ∀ n ∈ normalizer ((P : Subgroup G) : Set G), n * x * n⁻¹ ∈ zpowers x := by
    intro n hn
    apply hwc n
    rw [MonoidHom.map_zpowers, hQP]
    exact zpowers_le.mpr ((mem_normalizer_iff.mp hn x).mp hxP)
  have hcommle : ⁅(P : Subgroup G), normalizer ((P : Subgroup G) : Set G)⁆ ≤ T ⊔ Z := by
    rw [Subgroup.commutator_le]
    intro q hq n hn
    have hqC : q ∈ C := hPC hq
    have hm := hNx n⁻¹ (inv_mem hn)
    have hc : q⁻¹ ∈ C := inv_mem hqC
    have hnq : n * q⁻¹ * n⁻¹ ∈ (P : Subgroup G) :=
      (mem_normalizer_iff.mp hn _).mp (inv_mem hq)
    have hmc : n⁻¹⁻¹ * q⁻¹ * n⁻¹ ∈ C := by rw [inv_inv]; exact hPC hnq
    have hK := l28iv_hom_conj_mul_inv_mem hS hU0 hp hM hgen hJ hm hc hmc
    have hcP : ⁅q, n⁆ ∈ (P : Subgroup G) := by
      rw [commutatorElement_def, show q * n * q⁻¹ * n⁻¹ = q * (n * q⁻¹ * n⁻¹) by group]
      exact (P : Subgroup G).mul_mem hq hnq
    obtain ⟨hKn, -, -⟩ := l28_quot_data hS hU0 hp hM hgen hJ
    set qc : C := ⟨q, hqC⟩ with hqc
    set w : C := ⟨n⁻¹⁻¹ * q⁻¹ * n⁻¹, hmc⟩ * (⟨q⁻¹, hc⟩ : C)⁻¹ with hw
    have he : (⟨⁅q, n⁆, hPC hcP⟩ : C) = qc * w * qc⁻¹ := by
      apply Subtype.ext
      change ⁅q, n⁆ = q * (n⁻¹⁻¹ * q⁻¹ * n⁻¹ * q⁻¹⁻¹) * q⁻¹
      rw [commutatorElement_def]
      group
    have hπ : l34Hom x J ⟨⁅q, n⁆, hPC hcP⟩ ∈ l34Img x J J := by
      rw [he, map_mul, map_mul, map_inv]
      exact hKn.conj_mem _ hK _
    exact l28iv_mem_sup_of_hom_mem hS hU0 hK1 hp hM hgen hJ (c := ⟨⁅q, n⁆, hPC hcP⟩) hcP hπ
  obtain ⟨z₀', hz₀'⟩ := hZc.exists_generator
  set z₀ : G := (z₀' : G) with hz₀
  have hZeq : Z = zpowers z₀ := by
    refine le_antisymm (fun g hg => ?_) (zpowers_le.mpr z₀'.2)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hz₀' ⟨g, hg⟩)
    exact mem_zpowers_iff.mpr ⟨k, by rw [hz₀]; simpa using congrArg Subtype.val hk⟩
  have ht₀T : t₀ ∈ T := by rw [hT]; exact mem_zpowers t₀
  have hz₀P : z₀ ∈ (P : Subgroup G) := (hZQ z₀'.2).1
  set tP : ↥(P : Subgroup G) := ⟨t₀, ht₀T.1⟩ with htP
  set zP : ↥(P : Subgroup G) := ⟨z₀, hz₀P⟩ with hzP
  have htz : tP * zP = zP * tP := Subtype.ext (hcomm t₀ ht₀T z₀ z₀'.2)
  have hmap : (zpowers tP ⊔ zpowers zP).map (P : Subgroup G).subtype = T ⊔ Z := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hT, hZeq]
    rfl
  have hidx : Nat.card ↥(P : Subgroup G) ≤ 3 * Nat.card ↥(zpowers tP ⊔ zpowers zP) := by
    have h1 := l28iv_card_le hS hU0 hK1 hp hM hgen hJ
    rw [hQP, ← hmap, Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective] at h1
    exact h1
  have hW : ∀ (K : Subgroup ↥(P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃*
        (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) := fun K _ =>
    l28iv_isEmpty_quotient_wreath htz hidx K
  have hY := CFSG.RankThree.Transfer.yoshida_eq_commutator_normalizer_of_oResidual_eq_top P hW
    (l28iv_oResidual_eq_top hS)
  have hle : (P : Subgroup G) ≤ T ⊔ Z := by
    rw [hY]
    exact hcommle
  obtain ⟨y, hyQ, -, hyout⟩ := l28iv_exists_outside hS hU0 hK1 hp hM hgen hJ
  exact hyout (hle hyQ.1)

end CFSG.LocalAnalysis.RankThreeTheoremC
