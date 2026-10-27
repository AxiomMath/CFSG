module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorGeneration
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorConjugation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG
open scoped commutatorElement

universe u v

theorem full_odd_four_group_two_centralizer_commutator_generation
    {A : Type u} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    {I : Type v} [Group I] [Finite I] [MulDistribMulAction A I]
    (hcard : Nat.card A = 4) (a b : A)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (hodd : Odd (Nat.card I)) :
    actorCommutatorSubgroup b (⊤ : Subgroup I) =
      actorCommutatorSubgroup b (actorFixedSubgroup (I := I) a) ⊔
        actorCommutatorSubgroup b (actorFixedSubgroup (I := I) (a * b)) :=
  odd_elementary_four_group_two_centralizer_commutator_generation hcard a b ha hb hab hodd

variable {G : Type u} [Group G]

theorem odd_four_group_ambient_commutator_generation (J : Subgroup G) [Finite J]
    (u t : G) (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hut : u ≠ t) (hcomm : Commute u t)
    (huN : u ∈ Subgroup.normalizer (J : Set G))
    (htN : t ∈ Subgroup.normalizer (J : Set G)) (hodd : Odd (Nat.card J)) :
    ⁅J, Subgroup.zpowers t⁆ =
      ⁅J ⊓ Subgroup.centralizer {u}, Subgroup.zpowers t⁆ ⊔
        ⁅J ⊓ Subgroup.centralizer {u * t}, Subgroup.zpowers t⁆ := by
  let V : Subgroup G := Subgroup.zpowers u ⊔ Subgroup.zpowers t
  let : IsKleinFour V :=
    LocalCriterionDegreeIdentity.generated_commuting_involutions_isKleinFour
      u t hu ht hut hcomm
  let : Finite V := IsKleinFour.instFinite
  have hV : V ≤ Subgroup.normalizer (J : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr huN) (Subgroup.zpowers_le.mpr htN)
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  let a : V := ⟨u, (show Subgroup.zpowers u ≤ V from le_sup_left) (Subgroup.mem_zpowers u)⟩
  let b : V := ⟨t, (show Subgroup.zpowers t ≤ V from le_sup_right) (Subgroup.mem_zpowers t)⟩
  have ha : a ≠ 1 := by
    intro h
    have h' : u = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at hu
    norm_num at hu
  have hb : b ≠ 1 := by
    intro h
    have h' : t = 1 := congrArg Subtype.val h
    rw [h', orderOf_one] at ht
    norm_num at ht
  have hab : a ≠ b := fun h => hut (congrArg Subtype.val h)
  have htt : t * t = 1 := by
    simpa only [ht, pow_two] using pow_orderOf_eq_one t
  have hgen := odd_four_group_two_centralizer_commutator_generation
    (I := J) a b ha hb hab hodd
  have hmap := congrArg (fun Q : Subgroup J => Q.map J.subtype) hgen
  have hwhole := normalized_commutator_map J V hV b htt (⊤ : Subgroup J)
  have hleft := normalized_commutator_map J V hV b htt (actorFixedSubgroup (I := J) a)
  have hright := normalized_commutator_map J V hV b htt
    (actorFixedSubgroup (I := J) (a * b))
  have haMap := normalized_fixed_map J V hV a
  have habMap := normalized_fixed_map J V hV (a * b)
  have htop : (⊤ : Subgroup J).map J.subtype = J := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [Subgroup.map_sup, hwhole, hleft, hright, htop, haMap, habMap] at hmap
  exact hmap

theorem commutator_zpowers_le_centralizer (Q : Subgroup G) (u t : G)
    (hQ : Q ≤ Subgroup.centralizer {u}) (hcomm : Commute u t) :
    ⁅Q, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer {u} :=
  Subgroup.commutator_le_of_le hQ
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm))

theorem involution_commutator_eq_bot_of_centralized (Q : Subgroup G) (t : G)
    (ht : orderOf t = 2) (hQ : Q ≤ Subgroup.centralizer {t}) :
    ⁅Q, Subgroup.zpowers t⁆ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have htt : t * t = 1 := by
    simpa only [ht, pow_two] using pow_orderOf_eq_one t
  rcases (mem_zpowers_of_square_one htt).mp hy with rfl | rfl
  · simp only [commutatorElement_one_right, Subgroup.mem_bot]
  · apply Subgroup.mem_bot.mpr
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hQ hx))

theorem odd_four_group_commutator_centralized (J : Subgroup G) [Finite J]
    (u t : G) (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hut : u ≠ t) (hcomm : Commute u t)
    (huN : u ∈ Subgroup.normalizer (J : Set G))
    (htN : t ∈ Subgroup.normalizer (J : Set G)) (hodd : Odd (Nat.card J))
    (hcut : J ⊓ Subgroup.centralizer {u * t} ≤ Subgroup.centralizer {t}) :
    ⁅J, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer {u} := by
  rw [odd_four_group_ambient_commutator_generation J u t hu ht hut hcomm huN htN hodd,
    involution_commutator_eq_bot_of_centralized _ t ht hcut, sup_bot_eq]
  exact commutator_zpowers_le_centralizer _ u t inf_le_right hcomm

theorem odd_four_group_reversed_commutator_centralized (J : Subgroup G) [Finite J]
    (u t : G) (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hut : u ≠ t) (hcomm : Commute u t)
    (huN : u ∈ Subgroup.normalizer (J : Set G))
    (htN : t ∈ Subgroup.normalizer (J : Set G)) (hodd : Odd (Nat.card J))
    (hcut : J ⊓ Subgroup.centralizer {u * t} ≤ Subgroup.centralizer {t}) :
    ⁅Subgroup.zpowers t, J⁆ ≤ Subgroup.centralizer {u} := by
  rw [Subgroup.commutator_comm]
  exact odd_four_group_commutator_centralized J u t hu ht hut hcomm huN htN hodd hcut

theorem odd_four_group_mem_commutator_centralizer (J : Subgroup G) [Finite J]
    (u t : G) (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hut : u ≠ t) (hcomm : Commute u t)
    (huN : u ∈ Subgroup.normalizer (J : Set G))
    (htN : t ∈ Subgroup.normalizer (J : Set G)) (hodd : Odd (Nat.card J))
    (hcut : J ⊓ Subgroup.centralizer {u * t} ≤ Subgroup.centralizer {t}) :
    u ∈ Subgroup.centralizer ((⁅Subgroup.zpowers t, J⁆ : Subgroup G) : Set G) := by
  have h := odd_four_group_reversed_commutator_centralized
    J u t hu ht hut hcomm huN htN hodd hcut
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (h hx)

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
