module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayD5Quot

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

private lemma u_card_zpowers_selfC {G : Type} [Group G] {x : G} (hx : x * x = 1)
    (hx1 : x ≠ 1) : Nat.card (zpowers (selfC x)) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime
  · apply Subtype.ext
    show x ^ 2 = 1
    rw [pow_two]
    exact hx
  · intro h1
    exact hx1 (congrArg Subtype.val h1)

theorem card_centralizer_eq_two_mul_card_twoSec {G : Type} [Group G] [Finite G] {x : G}
    (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card (centralizer ({x} : Set G)) = 2 * Nat.card (TwoSec x) := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (zpowers (selfC x) : Subgroup ↥(centralizer ({x} : Set G)))
  rw [hcard, u_card_zpowers_selfC hx hx1]
  exact mul_comm _ _

theorem two_pow_ten_dvd_card_twoSec {G : Type} [Group G] [Finite G] {x : G} (hx : x * x = 1)
    (hx1 : x ≠ 1) (h : 2 ^ 11 ∣ Nat.card (centralizer ({x} : Set G))) :
    2 ^ 10 ∣ Nat.card (TwoSec x) := by
  rw [card_centralizer_eq_two_mul_card_twoSec hx hx1] at h
  have h11 : 2 ^ 11 = 2 * 2 ^ 10 := by norm_num
  rw [h11] at h
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h

theorem card_le_four_of_card_le_eight_twoSec {G : Type} [Group G] [Finite G] {x : G}
    (hx : x * x = 1) (hx1 : x ≠ 1) (A : Subgroup G) (hAx : A ≤ centralizer ({x} : Set G))
    (hA : Group.IsPerfect ↥A)
    (h8 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer (A : Set G) →
      Q ≤ centralizer ({x} : Set G) → Nat.card Q ≤ 8)
    (U : Subgroup (TwoSec x)) (hU : IsPGroup 2 U)
    (hUA : U ≤ centralizer
      ((((A.subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (zpowers (selfC x)))) : Subgroup (TwoSec x)) : Set (TwoSec x))) :
    Nat.card U ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : zpowers (selfC x) ≤ Subgroup.center ↥(centralizer ({x} : Set G)) :=
    zpowers_le.2 (selfC_mem_center x)
  have hperf : Group.IsPerfect ↥(A.subgroupOf (centralizer ({x} : Set G))) := by
    haveI : Group.IsPerfect ↥A := hA
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hAx).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAx).symm.surjective
  refine card_le_four_of_card_le_eight (zpowers (selfC x)) hZ
    (u_card_zpowers_selfC hx hx1) (A.subgroupOf (centralizer ({x} : Set G))) hperf ?_ U hU hUA
  intro Q hQ hQA
  have hQp : IsPGroup 2 (Q.map (centralizer ({x} : Set G)).subtype) := hQ.map _
  have hle1 : Q.map (centralizer ({x} : Set G)).subtype ≤ centralizer (A : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := Subgroup.mem_centralizer_iff.mp (hQA hq) ⟨a, hAx ha⟩
      (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h1
  have h2 := h8 _ hQp hle1 (Subgroup.map_subtype_le Q)
  rwa [Subgroup.card_map_of_injective (centralizer ({x} : Set G)).subtype_injective] at h2

end CFSG.OddStandard.AltStdSec.SwapPartner
