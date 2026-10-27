module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootCentralizers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorRelative

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

open CFSG
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

universe u v

attribute [local instance] Classical.propDecidable

theorem kleinFour_prod_nonidentity {V : Type v} [Group V] [Fintype V] [DecidableEq V] [IsKleinFour V]
    (f : V → ℕ) (a b : V) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    ∏ x ∈ Finset.univ.erase (1 : V), f x = f a * f b * f (a * b) := by
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hab ((mul_eq_one_iff_eq_inv.mp h).trans (IsKleinFour.inv_eq_self b))
  have haba : a * b ≠ a := by
    intro h
    exact hb (mul_left_cancel (show a * b = a * 1 by simpa using h))
  have habb : a * b ≠ b := by
    intro h
    exact ha (mul_right_cancel (show a * b = 1 * b by simpa using h))
  have hset : Finset.univ.erase (1 : V) = ({a * b, a, b} : Finset V) := by
    rw [← IsKleinFour.eq_finset_univ ha hb hab]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [hset, Finset.prod_insert (by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ⟨haba, habb⟩)]
  rw [Finset.prod_insert (by simpa only [Finset.mem_singleton] using hab)]
  simp only [Finset.prod_singleton]
  ac_rfl

theorem normalized_odd_four_group_relative_index_identity
    {G : Type u} [Group G] [Finite G]
    (J V : Subgroup G) [IsElementaryAbelian 2 V]
    (hcardV : Nat.card V = 4) (hoddJ : Odd (Nat.card J))
    (hV : V ≤ Subgroup.normalizer (J : Set G)) (t : G)
    (htV : t ∈ Subgroup.centralizer (V : Set G)) :
    let : Fintype V := Fintype.ofFinite V
    (Subgroup.centralizer ({t} : Set G)).relIndex J *
        ((Subgroup.centralizer ({t} : Set G)).relIndex
          (J ⊓ Subgroup.centralizer (V : Set G))) ^ 2 =
      ∏ a ∈ Finset.univ.erase (1 : V),
        (Subgroup.centralizer ({t} : Set G)).relIndex
          (J ⊓ Subgroup.centralizer ({(a : G)} : Set G)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : IsKleinFour V := isKleinFour_of_elementary_card_four hcardV
  have hactors : 1 < (Finset.univ.erase (1 : V)).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      IsKleinFour.card_four']
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hactors
  have ha1 : a ≠ 1 := (Finset.mem_erase.mp ha).1
  have hb1 : b ≠ 1 := (Finset.mem_erase.mp hb).1
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  let K := (Subgroup.centralizer ({t} : Set G)).subgroupOf J
  let : CFSG.IsInvariant V J K := normalized_tCentralizer_invariant J V hV t htV
  have hindex := four_group_relative_index_identity (A := V) (I := J)
    a b ha1 hb1 hab hoddJ K
  have hKindex : K.index = (Subgroup.centralizer ({t} : Set G)).relIndex J := rfl
  have hcommon := normalized_common_fixed_relative_index J V hV t
  have haindex := normalized_actor_fixed_relative_index J V hV t a
  have hbindex := normalized_actor_fixed_relative_index J V hV t b
  have habindex := normalized_actor_fixed_relative_index J V hV t (a * b)
  change K.index * (K.relIndex (fixedPointSubgroup V J)) ^ 2 =
    K.relIndex (actorFixedSubgroup (I := J) a) *
      K.relIndex (actorFixedSubgroup (I := J) b) *
        K.relIndex (actorFixedSubgroup (I := J) (a * b)) at hindex
  rw [hKindex, hcommon, haindex, hbindex, habindex] at hindex
  dsimp only
  exact hindex.trans (kleinFour_prod_nonidentity
    (fun a : V => (Subgroup.centralizer ({t} : Set G)).relIndex
      (J ⊓ Subgroup.centralizer ({(a : G)} : Set G))) a b ha1 hb1 hab).symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
