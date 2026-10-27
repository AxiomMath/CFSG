module

import CFSG.GroupTheory.FrattiniQuotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def ThompsonNormalAbelianGen : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (P : Type) [Group P] [Finite P], IsPGroup p P → ∀ k : ℕ,
    (∀ A : Subgroup P, A.Normal → IsMulCommutative A → Group.rank A ≤ k) →
    ∀ B : Subgroup P, Group.rank B ≤ k * (k + 1) / 2

theorem rank_map_le_rank {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] (f : A →* B)
    (W : Subgroup A) : Group.rank (W.map f) ≤ Group.rank W :=
  Group.rank_le_of_surjective (f.subgroupMap W) (f.subgroupMap_surjective W)

theorem rank_eq_of_elementary {V : Type*} [Group V] [Finite V] {p : ℕ} (hp : p.Prime)
    (hcomm : ∀ a b : V, a * b = b * a) (hexp : ∀ a : V, a ^ p = 1) {k : ℕ}
    (hcard : Nat.card V = p ^ k) : Group.rank V = k := by
  have : Fact p.Prime := ⟨hp⟩
  have : CFSG.IsElementaryAbelian p V :=
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  rw [← CFSG.generatorRank_eq_group_rank]
  exact Nat.pow_right_injective hp.two_le
    ((CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := p) V).symm.trans hcard)

theorem rank_le_pRank_of_comm {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (B : Subgroup G) (hB : IsPGroup p B) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Group.rank B ≤ Open.pRank p B := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p B) := ⟨hB⟩
  obtain ⟨-, -, -, helem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hB
  refine le_pRank_of_pow_mem hp B ((frattini B).map B.subtype) hcomm (fun b hb => ?_) ?_
  · have h := CFSG.OrderReductions.FrattiniElementary.frattini_quotient_exponent p hB
      (QuotientGroup.mk (⟨b, hb⟩ : B))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    exact ⟨_, h, rfl⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective B.subtype_injective,
      Subgroup.index, CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := p) (B ⧸ frattini B),
      ← CFSG.generatorRank_eq_group_rank]
    exact Nat.pow_le_pow_right hp.pos
      (CFSG.generatorRank_le_generatorRank_quotient_frattini (p := p) B)

theorem rank_le_of_pRank_le (hT : ThompsonNormalAbelianGen) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {P : Subgroup G} (hP : IsPGroup p P) {r : ℕ}
    (hr : Open.pRank p P ≤ r) : Group.rank P ≤ r * (r + 1) / 2 := by
  have h := hT p hp hp2 P hP r (fun A _ hA => ?_) ⊤
  · rwa [← Group.rank_congr (Subgroup.topEquiv : (⊤ : Subgroup P) ≃* P)]
  · have hcomm : ∀ x ∈ A.map P.subtype, ∀ y ∈ A.map P.subtype, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have h := congrArg (fun z : A => ((z : P) : G)) (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      simpa using h
    calc Group.rank A = Group.rank (A.map P.subtype) :=
          Group.rank_congr (A.equivMapOfInjective _ P.subtype_injective)
      _ ≤ Open.pRank p (A.map P.subtype) :=
          rank_le_pRank_of_comm hp _ ((hP.to_subgroup A).map _) hcomm
      _ ≤ Open.pRank p P :=
          PreuniquenessRankFour.Helpers.pRank_mono p hp (Subgroup.map_subtype_le A)
      _ ≤ r := hr

theorem exists_isPGroup_map_mk_eq {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N : Subgroup H) [N.Normal] {Y : Subgroup (H ⧸ N)} (hY : IsPGroup p Y) :
    ∃ W : Subgroup H, IsPGroup p W ∧ W.map (QuotientGroup.mk' N) = Y := by
  set f := QuotientGroup.mk' N
  let g : Y.comap f →* Y := (f.comp (Y.comap f).subtype).codRestrict Y fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨⟨h, hy⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow p (Y.comap f)) := inferInstance
  have htop : (S : Subgroup (Y.comap f)).map g = ⊤ := by
    have h := (S.mapSurjective hg).is_maximal' (hY.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  refine ⟨(S : Subgroup (Y.comap f)).map (Y.comap f).subtype, S.isPGroup'.map _, ?_⟩
  have hcomp : f.comp (Y.comap f).subtype = Y.subtype.comp g := rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem exists_lift_rank {G : Type*} [Group G] [Finite G] {H : Subgroup G} {p : ℕ}
    [Fact p.Prime] (N : Subgroup H) [N.Normal] {Y : Subgroup (H ⧸ N)} (hY : IsPGroup p Y) :
    ∃ W : Subgroup G, IsPGroup p W ∧ W ≤ (Y.comap (QuotientGroup.mk' N)).map H.subtype ∧
      Group.rank Y ≤ Group.rank W := by
  obtain ⟨W, hWp, hWY⟩ := exists_isPGroup_map_mk_eq N hY
  refine ⟨W.map H.subtype, hWp.map _, Subgroup.map_mono (hWY ▸ Subgroup.le_comap_map _ W), ?_⟩
  calc Group.rank Y = Group.rank (W.map (QuotientGroup.mk' N)) := Subgroup.rank_congr hWY.symm
    _ ≤ Group.rank W := rank_map_le_rank _ W
    _ = Group.rank (W.map H.subtype) :=
      Group.rank_congr (W.equivMapOfInjective _ H.subtype_injective)

theorem lt_pRank_of_quotient (hT : ThompsonNormalAbelianGen) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {H L : Subgroup G} (N : Subgroup H) [N.Normal]
    {Y : Subgroup (H ⧸ N)} (hY : IsPGroup p Y)
    (hYL : (Y.comap (QuotientGroup.mk' N)).map H.subtype ≤ L) {r : ℕ}
    (hr : r * (r + 1) / 2 < Group.rank Y) : r < Open.pRank p L := by
  have hp : p.Prime := Fact.out
  obtain ⟨W, hWp, hWY, hrank⟩ := exists_lift_rank N hY
  by_contra hle
  have hWr : Open.pRank p W ≤ r :=
    (PreuniquenessRankFour.Helpers.pRank_mono p hp (hWY.trans hYL)).trans (not_lt.mp hle)
  have := rank_le_of_pRank_le hT hp hp2 hWp hWr
  omega

end CFSG.AGLEmbedding
