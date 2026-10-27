module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexBorelStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexQuotientParameter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImagesRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaCentralExtension

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ShultStronglyClosedTI.LocalTheta
open scoped IsMulCommutative

universe u

variable {F : Type u} [Group F] [Finite F]

theorem native_simple_bender_oddCore_eq_bot
    (hmodel : IsSimpleBenderGroup F) (B : Subgroup F) (hB : IsBorelSubgroup B) :
    CFSG.oddCore F = ⊥ := by
  let : IsSimpleGroup F := hmodel.isSimple
  have hstrong := (simpleBender_borel_rank_and_strong_embedding hmodel B hB).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore F) with
    hbot | htop
  · exact hbot
  · have hodd : Odd (Nat.card (CFSG.oddCore F)) :=
      CFSG.ComponentClassification.OddCore.odd_card F
    rw [htop, Subgroup.card_top] at hodd
    exact (hodd.not_two_dvd_nat
      ((even_iff_two_dvd.mp hstrong.2.1).trans B.card_subgroup_dvd_card)).elim

theorem native_borel_involutions_commute
    (hmodel : IsSimpleBenderGroup F) (B : Subgroup F) (hB : IsBorelSubgroup B)
    (x y : F) (hx : x ∈ B ∧ IsInvolution x) (hy : y ∈ B ∧ IsInvolution y) :
    Commute x y := by
  obtain ⟨hrank, hstrong⟩ := simpleBender_borel_rank_and_strong_embedding hmodel B hB
  exact properCommutingImages_corefree_involutions_commute B
    (native_strong_embedding_of_order_conditions hstrong) hrank
    (native_simple_bender_oddCore_eq_bot hmodel B hB) x y hx.1
    (orderOf_eq_prime_iff.mpr ⟨hx.2.sq_eq_one, hx.2.ne_one⟩) hy.1
    (orderOf_eq_prime_iff.mpr ⟨hy.2.sq_eq_one, hy.2.ne_one⟩)

theorem native_borel_whole_elementary_root_at_exponent
    (a : ℕ) (ha : 2 ≤ a) (hmodelAt : IsSimpleBenderGroupAtExponent a F)
    (hmodel : IsSimpleBenderGroup F) (B : Subgroup F) (hB : IsBorelSubgroup B) :
    let U := Subgroup.closure {x : F | x ∈ B ∧ IsInvolution x}
    ∃ i : ℕ, i ∈ ({1, 2, 3} : Set ℕ) ∧
      IsElementaryAbelian 2 U ∧ U ≤ B ∧
      (U : Set F) = {1} ∪ {x : F | x ∈ B ∧ IsInvolution x} ∧
      Nat.card U = 2 ^ a ∧ 4 ≤ Nat.card U ∧ B.index = (2 ^ a) ^ i + 1 := by
  let s : Set F := {x : F | x ∈ B ∧ IsInvolution x}
  let U := Subgroup.closure s
  have helem : IsElementaryAbelian 2 U :=
    square_one_commuting_closure_elementary s
      (fun x hx y hy _hne => native_borel_involutions_commute hmodel B hB x y hx hy)
      (fun x hx => hx.2.sq_eq_one)
  let : IsElementaryAbelian 2 U := helem
  have hUB : U ≤ B := (Subgroup.closure_le _).mpr (fun _ hx => hx.1)
  have hset : (U : Set F) = {1} ∪ s := by
    ext x
    constructor
    · intro hx
      by_cases hxone : x = 1
      · exact Or.inl (Set.mem_singleton_iff.mpr hxone)
      · exact Or.inr ⟨hUB hx, hxone, elemPow_eq_one_of_isElementaryAbelian x hx⟩
    · rintro (hx | hx)
      · obtain rfl := Set.mem_singleton_iff.mp hx
        exact U.one_mem
      · exact Subgroup.subset_closure hx
  obtain ⟨i, hi, hparameter⟩ := simpleBender_borel_exact_parameter_at_exponent a ha hmodelAt
  obtain ⟨hindex, hcount⟩ := hparameter B hB
  have hcard : Nat.card U = 2 ^ a := by
    change Nat.card ↥(U : Set F) = 2 ^ a
    rw [hset, identity_adjoined_whole_involution_card, hcount]
    have hpositive : 0 < 2 ^ a := pow_pos (by decide) a
    omega
  have hfour : 4 ≤ Nat.card U := by
    rw [hcard]
    simpa only [show 2 ^ 2 = 4 from rfl] using
      Nat.pow_le_pow_right (n := 2) (by omega) ha
  exact ⟨i, hi, helem, hUB, hset, hcard, hfour, hindex⟩

theorem native_borel_whole_elementary_root
    (hmodel : IsSimpleBenderGroup F) (B : Subgroup F) (hB : IsBorelSubgroup B) :
    let U := Subgroup.closure {x : F | x ∈ B ∧ IsInvolution x}
    ∃ a i : ℕ, 2 ≤ a ∧ i ∈ ({1, 2, 3} : Set ℕ) ∧
      IsElementaryAbelian 2 U ∧ U ≤ B ∧
      (U : Set F) = {1} ∪ {x : F | x ∈ B ∧ IsInvolution x} ∧
      Nat.card U = 2 ^ a ∧ 4 ≤ Nat.card U ∧ B.index = (2 ^ a) ^ i + 1 := by
  obtain ⟨a, ha, hmodelAt⟩ := hmodel.exists_exponent
  obtain ⟨i, hi, helem, hUB, hset, hcard, hfour, hindex⟩ :=
    native_borel_whole_elementary_root_at_exponent a ha hmodelAt hmodel B hB
  exact ⟨a, i, ha, hi, helem, hUB, hset, hcard, hfour, hindex⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
