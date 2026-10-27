module

public import CFSG.Assembly.OddCoreEliminationStatements
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistence
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type*} [Group G]

theorem assembly_isElemAbelian_iff_open (p : ℕ) (E : Subgroup G) :
    IsElemAbelian p E ↔ CFSG.Open.IsElemAbelian p E :=
  Iff.rfl

theorem assembly_pRank_eq_open [Finite G] (p : ℕ) (H : Subgroup G) :
    pRank p H = CFSG.Open.pRank p H :=
  rfl

theorem assembly_twoRank_eq_open (G : Type*) [Group G] [Finite G] :
    twoRank G = CFSG.Open.twoRank G :=
  rfl

theorem isPerfect_of_commutator_eq_top (h : commutator G = ⊤) : Group.IsPerfect G :=
  Group.isPerfect_def.mpr h

private theorem le_normalizer_map_subtype {S : Subgroup G} (V : Subgroup S) [V.Normal] :
    S ≤ Subgroup.normalizer ((V.map S.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := V) S.subtype
  rwa [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h

variable [Finite G]

theorem pRank_sylow_eq_twoRank (S : Sylow 2 G) : pRank 2 (S : Subgroup G) = twoRank G :=
  CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq S

private theorem pRank_eq_twoRank_subgroup (S : Subgroup G) :
    pRank 2 S = CFSG.Open.twoRank S :=
  CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide) S

theorem exists_normal_four_of_three_le_pRank {S : Subgroup G} (hS : IsPGroup 2 S)
    (h3 : 3 ≤ pRank 2 S) :
    ∃ V : Subgroup G, V ≤ S ∧ S ≤ Subgroup.normalizer (V : Set G) ∧ IsElemAbelian 2 V ∧
      Nat.card V = 4 := by
  rw [pRank_eq_twoRank_subgroup] at h3
  obtain ⟨V, hVn, hV, hV4⟩ := CFSG.ProperTwoGeneratedCore.high_two_rank_normal_four S hS h3
  refine ⟨V.map S.subtype, Subgroup.map_subtype_le V, le_normalizer_map_subtype V,
    CFSG.LargeEvenClassification.Helpers.elementary_map V hV S.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective S.subtype_injective, hV4]

theorem exists_involution_inf_subgroupCenter {S U : Subgroup G} (hS : IsPGroup 2 S)
    (hUS : U ≤ S) (hU : S ≤ Subgroup.normalizer (U : Set G)) (hne : U ≠ ⊥) :
    ∃ z ∈ U ⊓ subgroupCenter S, orderOf z = 2 := by
  have : (U.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUS).mpr hU
  have hne' : U.subgroupOf S ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun h => hne (disjoint_iff.mp h ▸ (inf_eq_left.mpr hUS).symm)
  obtain ⟨hdvd, -⟩ := CFSG.SectionRank.Ccomm.normal_inf_center_card (p := 2) hS hne'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxU : ((x : S) : G) ∈ U := (Subgroup.mem_inf.mp x.2).1
  have hxZ : (x : S) ∈ Subgroup.center S := (Subgroup.mem_inf.mp x.2).2
  have hxC : ((x : S) : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨s, hs⟩)
  refine ⟨((x : S) : G), Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_inf.mpr ⟨(x : S).2, hxC⟩⟩, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

theorem exists_elemAbelian_eight_le_centralizer {S V A : Subgroup G} (hS : IsPGroup 2 S)
    (hVS : V ≤ S) (hSV : S ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4) (hAS : A ≤ S) (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) :
    ∃ U : Subgroup G, U ≤ S ⊓ Subgroup.centralizer (V : Set G) ∧ V ≤ U ∧ IsElemAbelian 2 U ∧
      8 ≤ Nat.card U := by
  let V' := V.subgroupOf S
  let A' := A.subgroupOf S
  have : V'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVS).mpr hSV
  have hV' : CFSG.Open.IsElemAbelian 2 V' :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 2 V V'
      (Subgroup.subgroupOfEquivOfLe hVS).symm hV
  have hV'4 : Nat.card V' = 4 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv).trans hV4
  have hA' : CFSG.Open.IsElemAbelian 2 A' :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport 2 A A'
      (Subgroup.subgroupOfEquivOfLe hAS).symm hA
  have hA'8 : Nat.card A' = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv).trans hA8
  obtain ⟨-, hUC, hVU, hU, hU8, -⟩ :=
    CFSG.ProperTwoGeneratedCore.normal_four_centralizer_rank_three hS V' hV' hV'4 A' hA' hA'8
  set U := (A' ⊓ Subgroup.centralizer (V' : Set S)) ⊔ V'
  refine ⟨U.map S.subtype, le_inf (Subgroup.map_subtype_le U) ?_, ?_,
    CFSG.LargeEvenClassification.Helpers.elementary_map U hU S.subtype, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (hUC hu) ⟨v, hVS hv⟩ (show v ∈ V from hv))
  · rw [← Subgroup.map_subgroupOf_eq_of_le hVS]
    exact Subgroup.map_mono hVU
  · rwa [Subgroup.card_map_of_injective S.subtype_injective]

theorem three_le_pRank_inf_centralizer {S V A : Subgroup G} (hS : IsPGroup 2 S)
    (hVS : V ≤ S) (hSV : S ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4) (hAS : A ≤ S) (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) :
    3 ≤ pRank 2 (S ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨U, hUC, -, hU, hU8⟩ :=
    exists_elemAbelian_eight_le_centralizer hS hVS hSV hV hV4 hAS hA hA8
  obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup 2 U hU).exists_card_eq
  have h3 : 3 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hk] using hU8
  exact h3.trans (le_csSup
    (CFSG.RankThreeCoreUniqueness.Helpers.pRank_set_bddAbove 2 (by decide) _) ⟨U, hUC, hU, hk⟩)

end CFSG.Assembly.Dichotomy
