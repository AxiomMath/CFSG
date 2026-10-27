module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RowCT

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Ree (ReeTag)

section Span

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def twoE6Span (e : L ≃* adjointGroup .F4 K)
    (X₀ : Subgroup (adjointGroup .F4 K)) : Subgroup G :=
  centralizerPerfectCore (subgroupToG e X₀) ⊔ L

theorem le_twoE6Span (e : L ≃* adjointGroup .F4 K) (X₀ : Subgroup (adjointGroup .F4 K)) :
    L ≤ twoE6Span e X₀ :=
  le_sup_right

theorem centralizerPerfectCore_le_twoE6Span (e : L ≃* adjointGroup .F4 K)
    (X₀ : Subgroup (adjointGroup .F4 K)) :
    centralizerPerfectCore (subgroupToG e X₀) ≤ twoE6Span e X₀ :=
  le_sup_left

theorem mem_normalizer_twoE6Span (e : L ≃* adjointGroup .F4 K)
    (X₀ : Subgroup (adjointGroup .F4 K)) {t : G} (htC : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer (twoE6Span e X₀ : Set G) := by
  have htX : t ∈ centralizer (subgroupToG e X₀ : Set G) :=
    centralizer_le (map_subtype_le _) htC
  have hA : t ∈ normalizer (centralizerPerfectCore (subgroupToG e X₀) : Set G) :=
    normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ htX)
  have hB : t ∈ normalizer (L : Set G) := centralizer_le_normalizer L htC
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [twoE6Span, Subgroup.map_sup, hA, hB]

theorem twoE6Span_ne_bot (e : L ≃* adjointGroup .F4 K) (X₀ : Subgroup (adjointGroup .F4 K)) :
    twoE6Span e X₀ ≠ ⊥ := by
  intro hbot
  have := CFSG.LieType.Chevalley.nontrivial_adjointGroup_F4 (K := K)
  obtain ⟨x, hx⟩ := exists_ne (1 : adjointGroup Tag.F4 K)
  apply hx
  have h1 : ((e.symm x : L) : G) ∈ twoE6Span e X₀ := le_twoE6Span e X₀ (e.symm x).2
  rw [hbot, mem_bot] at h1
  have h2 : e.symm x = 1 := Subtype.ext h1
  rw [← e.apply_symm_apply x, h2, map_one]

end Span

section Inputs


@[expose] def TwoE6FamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∃ φ : ∀ J, (e6Datum K).leviAmalgam J →* G, IsTwoE6GraphFamily (twoE6Span e X₀) t K φ

@[expose] def TwoE6UniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∀ φ : ∀ J, (e6Datum K).leviAmalgam J →* G, IsTwoE6GraphFamily (twoE6Span e X₀) t K φ →
      ∀ g : G, g⁻¹ * t * g ∈ normalizer (twoE6Span e X₀ : Set G) →
        g ∈ normalizer (twoE6Span e X₀ : Set G)

end Inputs

section Row


theorem exists_mulEquiv_twoE6Span_of_family {G : Type} [Group G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K)
    (X₀ : Subgroup (adjointGroup .F4 K)) {t : G} (htC : t ∈ centralizer (L : Set G))
    {φ : ∀ J, (e6Datum K).leviAmalgam J →* G} (hφ : IsTwoE6GraphFamily (twoE6Span e X₀) t K φ) :
    center (twoE6Span e X₀) = ⊥ ∧
      ∃ e₆ : twoE6Span e X₀ ⧸ center (twoE6Span e X₀) ≃* adjointGroup Tag.E6 K,
        EPilot.normalizerQuotMulAut e₆ ⟨t, mem_normalizer_twoE6Span e X₀ htC⟩ =
          exactNormalAut Tag.E6 K 1 (RingEquiv.refl K) 1 :=
  ⟨center_eq_bot_of_isTwoE6GraphFamily hK (twoE6Span_ne_bot e X₀) hφ,
    exists_center_quotient_graph_of_isTwoE6GraphFamily (mem_normalizer_twoE6Span e X₀ htC)
      (twoE6Span_ne_bot e X₀) hφ⟩

theorem twoKindPairInput_linear6_omegaMinus8_of_inputs (hF : TwoE6FamilyInput)
    (hU : TwoE6UniqueInput) : TwoKindPairInput .linear6 .omegaMinus8 := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ'
  obtain ⟨φ, hφ⟩ := hF G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ'
  have huniq := hU G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' φ hφ
  have htN := mem_normalizer_twoE6Span e X₀ hw.mem_centralizer
  obtain ⟨e₆, hnf⟩ :=
    exists_center_quotient_graph_normalForm_of_isTwoE6GraphFamily htN (twoE6Span_ne_bot e X₀) hφ
  have := hw.standard.simple
  exact EPilot.false_of_simple_of_E6_conj_graph_quot K e₆ htN hw.orderOf_eq hnf huniq

theorem twoE6PairInput_of_inputs (hF : TwoE6FamilyInput) (hU : TwoE6UniqueInput) :
    TwoE6PairInput :=
  twoE6PairInput_of_linear6 (twoKindPairInput_linear6_omegaMinus8_of_inputs hF hU)

end Row

end CFSG.SeitzReduction.F4Pilot
