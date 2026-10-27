module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3Config
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

structure BenderHyp (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  standard : standardComponentIsStandard L
  oddCore : standardComponentOddCore G = ⊥
  not_normal : ¬ L.Normal
  rank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))
  bender : RankTwoBenderType (rankTwoQuot L)

@[expose] def BenderConclusion {G : Type} [Group G] (L : Subgroup G) : Prop :=
  CFSG.Blueprint.SuzukiModel (rankTwoQuot L) 2 3 ∧
    CFSG.Blueprint.NativeSporadic.IsSporadic (rankTwoX L) .Ru

section Standard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_subgroupOf_eq {L H : Subgroup G} (hLH : L ≤ H) :
    centralizer ((L.subgroupOf H : Subgroup H) : Set H) =
      (centralizer (L : Set G) ⊓ H).subgroupOf H := by
  rw [AS76b.Lemma37.centralizer_subgroupOf hLH, inf_subgroupOf_right]

omit [Finite G] in
theorem standard_subgroupOf {L H : Subgroup G} (hstd : standardComponentIsStandard L)
    (hLH : L ≤ H) (heven : Even (Nat.card (centralizer (L : Set G) ⊓ H : Subgroup G))) :
    standardComponentIsStandard (L.subgroupOf H) :=
  CFSG.Open.standardComponentIsStandard.subgroupOf hstd hLH heven

theorem IsSylowOf.exists_map_conj {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : IsSylowOf p P K) (h' : IsSylowOf p P' K) :
    ∃ k ∈ K, P' = P.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨S, rfl⟩ := h
  obtain ⟨S', rfl⟩ := h'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S S'
  refine ⟨k, k.2, ?_⟩
  rw [← hk]
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    refine ⟨K.subtype ((MulAut.conj k)⁻¹ • y), ⟨_, hy, rfl⟩, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨MulAut.conj k s, ?_, ?_⟩
    · rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hs
    · simp [MulAut.conj_apply]

theorem exists_elemAbelian_four_le_of_isSylowOf {K T : Subgroup G}
    (hK : 2 ≤ Open.pRank 2 K) (hT : IsSylowOf 2 T K) :
    ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEK, hE, hE4⟩ := AS76b.exists_elemAbelian_four (by omega : 1 < Open.pRank 2 K)
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨S, hS, hES⟩ := AS76b.exists_isSylowOf_le hEK hE2
  obtain ⟨k, -, hk⟩ := IsSylowOf.exists_map_conj hS hT
  refine ⟨E.map (MulAut.conj k).toMonoidHom, hk ▸ map_mono hES, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    simp only [coe_mul]
    have hxy : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  · rw [card_map_of_injective (MulAut.conj k).injective, hE4]

theorem two_le_pRank_of_le {E H : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 2 E)
    (hE4 : Nat.card E = 4) : 2 ≤ Open.pRank 2 H := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEH, hE, by rw [hE4]; norm_num⟩
  rintro k ⟨F, -, -, hF⟩
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ = Nat.card F := hF.symm
    _ ≤ Nat.card G := card_le_card_group F

end Standard

namespace BenderHyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem hyp31 (h : BenderHyp G L) :
    AS76b.Hyp31 L :=
  hyp31_of_standard h.standard h.oddCore h.not_normal h.rank h.bender

theorem rankTwoX_eq
    (h : BenderHyp G L) : rankTwoX L = CFSG.generalizedFitting G :=
  (AS76b.asc08Lemma34 G L h.hyp31).1

theorem isSimpleGroup_X
    (h : BenderHyp G L) : IsSimpleGroup (rankTwoX L) := by
  have h34 := AS76b.asc08Lemma34 G L h.hyp31
  change IsSimpleGroup ↥(normalClosure (L : Set G))
  rw [h34.1]
  exact h34.2

theorem exists_not_commute (h : BenderHyp G L) : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a :=
  AS76b.Lemma34.exists_not_commute h.standard.1

theorem center_X_eq_bot
    (h : BenderHyp G L) : center (rankTwoX L) = ⊥ := by
  have := h.isSimpleGroup_X
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (rankTwoX L)) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := h.exists_not_commute
    have hc' : (⟨a, le_normalClosure ha⟩ : rankTwoX L) ∈ center (rankTwoX L) := hc ▸ mem_top _
    exact hab (congrArg Subtype.val ((mem_center_iff.mp hc' ⟨b, le_normalClosure hb⟩).symm))

theorem centralizer_X_eq_bot
    (h : BenderHyp G L) : centralizer (rankTwoX L : Set G) = ⊥ := by
  have hle : centralizer (rankTwoX L : Set G) ≤ rankTwoX L := by
    rw [h.rankTwoX_eq]
    exact CFSG.centralizer_generalizedFitting_le G
  have hZ := h.center_X_eq_bot
  rw [eq_bot_iff]
  intro c hc
  have hcZ : (⟨c, hle hc⟩ : rankTwoX L) ∈ center (rankTwoX L) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hc y y.2)
  rw [hZ, mem_bot] at hcZ
  rw [mem_bot]
  exact congrArg Subtype.val hcZ

theorem le_of_normal
    (h : BenderHyp G L) {N : Subgroup G} (hN : N.Normal) (hN1 : N ≠ ⊥) : rankTwoX L ≤ N := by
  have := h.isSimpleGroup_X
  have hX : (rankTwoX L).Normal := normalClosure_normal
  rcases (hN.subgroupOf (rankTwoX L)).eq_bot_or_eq_top with hb | ht
  · exfalso
    apply hN1
    have hdis : N ⊓ rankTwoX L = ⊥ := by
      rw [← disjoint_iff]
      exact (subgroupOf_eq_bot).mp hb
    have hc : ⁅N, rankTwoX L⁆ = ⊥ := le_bot_iff.mp (hdis ▸ commutator_le_inf N (rankTwoX L))
    rw [← le_bot_iff, ← h.centralizer_X_eq_bot]
    exact (commutator_eq_bot_iff_le_centralizer).mp hc
  · exact (subgroupOf_eq_top).mp ht

theorem fitting_eq_bot
    (h : BenderHyp G L) : CFSG.fittingSubgroup G = ⊥ := by
  by_contra hF
  have hXF := h.le_of_normal inferInstance hF
  have : Group.IsNilpotent (CFSG.fittingSubgroup G) := inferInstance
  have : Group.IsNilpotent ((rankTwoX L).subgroupOf (CFSG.fittingSubgroup G)) := inferInstance
  have : Group.IsNilpotent (rankTwoX L) :=
    Group.nilpotent_of_mulEquiv (subgroupOfEquivOfLe hXF)
  have : Nontrivial (rankTwoX L) := by
    obtain ⟨a, ha, b, hb, hab⟩ := h.exists_not_commute
    refine ⟨⟨⟨a, le_normalClosure ha⟩, ⟨b, le_normalClosure hb⟩, fun he => hab ?_⟩⟩
    rw [show a = b from congrArg Subtype.val he]
  exact Group.IsNilpotent.center_ne_bot (rankTwoX L) h.center_X_eq_bot

@[expose] noncomputable def quotEquivSubgroupOf {H : Subgroup G} (hLH : L ≤ H) :
    rankTwoQuot (L.subgroupOf H) ≃* rankTwoQuot L :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLH) (RankTwoBender.map_center_mulEquiv _)

end BenderHyp

end CFSG.ComponentClassification.GMS78
