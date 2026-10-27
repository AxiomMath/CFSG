module

public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G] [Finite G]

theorem generatedPairGrowth_sylow_intersection_normal
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (P : Sylow p G) :
    ∃ R : Sylow p N,
      (R : Subgroup N).map N.subtype = (P : Subgroup G) ⊓ N := by
  let : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' N
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective N)
  let U := (P : Subgroup G).subgroupOf N
  have hUp : IsPGroup p U := P.isPGroup'.comap_subtype
  have hc : Nat.card (N.subgroupOf (P : Subgroup G)) = Nat.card U := by
    calc
      Nat.card (N.subgroupOf (P : Subgroup G)) =
          Nat.card ((N.subgroupOf (P : Subgroup G)).map (P : Subgroup G).subtype) :=
        (Subgroup.card_subtype (P : Subgroup G)
          (N.subgroupOf (P : Subgroup G))).symm
      _ = Nat.card ((P : Subgroup G) ⊓ N : Subgroup G) := by
        rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = Nat.card U := by
        rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
  have hPcard : Nat.card U * Nat.card (Q : Subgroup (G ⧸ N)) =
      Nat.card (P : Subgroup G) := by
    have h := (N.subgroupOf (P : Subgroup G)).card_mul_index
    rw [hc] at h
    change Nat.card U * N.relIndex (P : Subgroup G) = _ at h
    have hi := Subgroup.relIndex_ker (P : Subgroup G) q
    rw [QuotientGroup.ker_mk'] at hi
    rw [hi] at h
    simpa only [Q, Sylow.coe_mapSurjective] using h
  have hGcard : Nat.card N * Nat.card (G ⧸ N) = Nat.card G := by
    simpa only [Subgroup.index_eq_card] using N.card_mul_index
  have hPfac := congrArg (fun n : ℕ => n.factorization p) hPcard
  have hGfac := congrArg (fun n : ℕ => n.factorization p) hGcard
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at hPfac hGfac
  have heQ : (Nat.card (Q : Subgroup (G ⧸ N))).factorization p =
      (Nat.card (G ⧸ N)).factorization p := by
    rw [Q.card_eq_multiplicity, Nat.factorization_pow_self hp]
  have heP : (Nat.card (P : Subgroup G)).factorization p =
      (Nat.card G).factorization p := by
    rw [P.card_eq_multiplicity, Nat.factorization_pow_self hp]
  rw [heQ, heP] at hPfac
  have heU : (Nat.card U).factorization p = (Nat.card N).factorization p :=
    Nat.add_right_cancel (hPfac.trans hGfac.symm)
  obtain ⟨n, hn⟩ := hUp.exists_card_eq
  have hnfac : n = (Nat.card N).factorization p := by
    rw [hn, Nat.factorization_pow_self hp] at heU
    exact heU
  have hUcard : Nat.card U = p ^ (Nat.card N).factorization p := hn.trans (congrArg (p ^ ·) hnfac)
  refine ⟨Sylow.ofCard U hUcard, ?_⟩
  rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype]

theorem generatedPairGrowth_full_prime_part_of_sylow_contained
    {p : ℕ} (hp : p.Prime) (V J : Subgroup G) (hVJ : V ≤ J) (P : Sylow p J)
    (hPV : (P : Subgroup J).map J.subtype ≤ V) :
    (Nat.card V).factorization p = (Nat.card J).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hVJ) p
  · have hd := Subgroup.card_dvd_of_le hPV
    rw [Subgroup.card_subtype, P.card_eq_multiplicity] at hd
    have he := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero)
      Nat.card_pos.ne').mpr hd p
    rwa [Nat.factorization_pow_self hp] at he

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
