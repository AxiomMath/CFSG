module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG

open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G]

instance perfectResidual_characteristic' : (perfectResidual G).Characteristic :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic (G := G)

theorem exists_perfectResidual_eq_derivedSeries [Finite G] :
    ∃ n : ℕ, perfectResidual G = derivedSeries G n ∧
      derivedSeries G n = derivedSeries G (n + 1) := by
  obtain ⟨n, hn⟩ := finite_perfectResidual_eq_derivedSeries (G := G)
  refine ⟨n, hn, le_antisymm ?_ (derivedSeries_antitone G (Nat.le_succ n))⟩
  rw [← hn]
  exact iInf_le _ (n + 1)

theorem isSolvable_quotient_iff_exists_derivedSeries_le (N : Subgroup G) [N.Normal] :
    Group.IsSolvable (G ⧸ N) ↔ ∃ r : ℕ, derivedSeries G r ≤ N := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    have h := map_derivedSeries_eq (QuotientGroup.mk'_surjective N) r
    rw [hr, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective N) r, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hr

theorem perfect_residual_characterization [Finite G] :
    (∃ n : ℕ, perfectResidual G = derivedSeries G n ∧
      derivedSeries G n = derivedSeries G (n + 1)) ∧
    (perfectResidual G).Characteristic ∧ Group.IsPerfect (perfectResidual G) ∧
    Group.IsSolvable (G ⧸ perfectResidual G) ∧
    (∀ (N : Subgroup G) [N.Normal], Group.IsSolvable (G ⧸ N) ↔ perfectResidual G ≤ N) ∧
    (perfectResidual G = ⊥ ↔ Group.IsSolvable G) := by
  obtain ⟨n, hn, -⟩ := exists_perfectResidual_eq_derivedSeries (G := G)
  have hiff : ∀ (N : Subgroup G) [N.Normal], Group.IsSolvable (G ⧸ N) ↔ perfectResidual G ≤ N := by
    intro N _
    rw [isSolvable_quotient_iff_exists_derivedSeries_le]
    constructor
    · rintro ⟨r, hr⟩
      exact (iInf_le _ r).trans hr
    · intro h
      exact ⟨n, hn ▸ h⟩
  refine ⟨exists_perfectResidual_eq_derivedSeries, inferInstance,
    finite_perfectResidual_isPerfect (G := G), (hiff _).mpr le_rfl, hiff,
    finite_perfectResidual_eq_bot_iff_solvable (G := G)⟩

theorem perfect_residual_transport {H : Type*} [Group H] [Finite G] [Finite H] (f : G →* H) :
    (perfectResidual G).map f = (perfectResidual f.range).map f.range.subtype ∧
    (∀ U : Subgroup G, (perfectResidual U).map U.subtype ≤ perfectResidual G) ∧
    (∀ P : Subgroup G, Group.IsPerfect P → P ≤ perfectResidual G) := by
  have hperf : ∀ P : Subgroup G, Group.IsPerfect P → P ≤ perfectResidual G :=
    fun P hP => perfect_subgroup_le_perfectResidual P hP
  refine ⟨?_, ?_, hperf⟩
  · have h := finite_perfectResidual_map_eq (G := G) f.rangeRestrict f.rangeRestrict_surjective
    rw [← show (perfectResidual f.range) =
      CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual f.range from rfl] at h
    rw [← h, Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    rfl
  · intro U
    apply hperf
    have hP : Group.IsPerfect (perfectResidual U) := finite_perfectResidual_isPerfect (G := U)
    rw [Subgroup.isPerfect_iff] at hP ⊢
    rw [← Subgroup.map_commutator, hP]

end CFSG
