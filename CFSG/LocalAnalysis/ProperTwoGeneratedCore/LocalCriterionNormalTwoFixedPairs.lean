module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedMaximality

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem prime_dividing_point_class_odd_part_gt_one
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card (conjugacyWithin H z)) :
    Odd p ∧ 1 < p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  have hmOdd := point_subgroup_full_class_card_odd h S hzS hzcenter
  have hnonzero : Nat.card (conjugacyWithin H z) ≠ 0 := by
    intro hzero
    rw [hzero] at hmOdd
    exact (by decide : ¬ Odd (0 : ℕ)) hmOdd
  have hexp := hp.factorization_pos_of_dvd hnonzero hdiv
  exact ⟨hmOdd.of_dvd_nat hdiv, one_lt_pow₀ hp.one_lt hexp.ne'⟩

theorem pair_sylow_whole_fixed_set
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q)
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card (conjugacyWithin H z))
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (P : Sylow p (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)) :
    pointFixedSet H
      ((P : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype) = {a, b} := by
  let B := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let PG : Subgroup G := (P : Subgroup B).map B.subtype
  have hPGp : IsPGroup p PG := P.isPGroup'.map B.subtype
  have hPGB : PG ≤ B := Subgroup.map_subtype_le _
  have ha : a ∈ pointFixedSet H PG := (mem_pointFixedSet_iff H PG a).mpr
    (hPGB.trans inf_le_left)
  have hb : b ∈ pointFixedSet H PG := (mem_pointFixedSet_iff H PG b).mpr
    (hPGB.trans inf_le_right)
  obtain ⟨hodd, hpart⟩ := prime_dividing_point_class_odd_part_gt_one h S hzS hzcenter p hp hdiv
  obtain ⟨r, hr, _, _, hrP, hmotion⟩ := pair_specified_sylow_flip h S hzS hzcenter a b hab p hp P
  exact pointFixedSet_eq_pair_of_card_le_two H PG a b hab ha hb
    (full_motion_fixed_card_le_two h S hzS hzcenter hQH hQnormal hQtwo hzQ
      p hp hodd hpart hPGp r hr hrP hmotion)

theorem odd_p_normalizer_fixes_whole_pair
    (H M U : Subgroup G) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hU : IsPGroup p U) (hUN : U ≤ Subgroup.normalizer (M : Set G))
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (hpair : pointFixedSet H M = {a, b}) :
    U ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b := by
  have hcard : Nat.card (pointFixedSet H M) = 2 := by
    rw [hpair]
    exact Set.ncard_pair hab
  have hmod := pointFixedSet_restricted_card_modEq p hp H M U hU hUN
  rw [hcard] at hmod
  have hinterCard : 2 ≤ Nat.card (pointFixedSet H M ∩ pointFixedSet H U : Set _) :=
    two_le_of_modEq_two p _ hp hodd hmod.symm
  have hinter : pointFixedSet H M ∩ pointFixedSet H U = pointFixedSet H M := by
    apply Set.eq_of_subset_of_ncard_le Set.inter_subset_left
    change Nat.card (pointFixedSet H M) ≤
      Nat.card (pointFixedSet H M ∩ pointFixedSet H U : Set _)
    rw [hcard]
    exact hinterCard
  have hsub : pointFixedSet H M ⊆ pointFixedSet H U := by
    intro x hx
    have hh : x ∈ pointFixedSet H M ∩ pointFixedSet H U := hinter.symm ▸ hx
    exact hh.2
  have haU : a ∈ pointFixedSet H U := hsub (hpair.symm ▸ Set.mem_insert a {b})
  have hbU : b ∈ pointFixedSet H U := hsub (hpair.symm ▸ Set.mem_insert_of_mem a rfl)
  exact le_inf ((mem_pointFixedSet_iff H U a).mp haU)
    ((mem_pointFixedSet_iff H U b).mp hbU)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
