module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt
import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

public section

namespace CFSG.GroupTheory

universe u v

theorem mem_zpowers_of_isKleinFour {A : Type*} [Group A] [IsKleinFour A] (a g : A) :
    g ∈ Subgroup.zpowers a ↔ g = 1 ∨ g = a := by
  constructor
  · intro hg
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hz : a ^ z = a ^ (z % (2 : ℕ)) := zpow_eq_zpow_emod' z (by
      rw [pow_two]
      exact IsKleinFour.mul_self a)
    have hcases : z % (2 : ℕ) = 0 ∨ z % (2 : ℕ) = 1 := by omega
    rcases hcases with h | h
    · left
      rw [hz, h, zpow_zero]
    · right
      rw [hz, h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem card_mul_card_fixedPointSubgroup_sq_of_universe {A X : Type u} [Group A] [IsKleinFour A]
    [Fintype A] [DecidableEq A] [Group X] [Finite X] [MulDistribMulAction A X]
    (hX : Odd (Nat.card X)) :
    Nat.card X * Nat.card (fixedPointSubgroup A X) ^ 2 =
      ∏ a ∈ Finset.univ.erase (1 : A), Nat.card (fixedPointSubgroup (Subgroup.zpowers a) X) := by
  classical
  have hA4 : Nat.card A = 4 := IsKleinFour.card_four
  have hcop : Nat.Coprime (Nat.card X) (Nat.card A) := by
    rw [hA4, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hX)
  have hsolv : Group.IsSolvable X := CFSG.FeitThompson.isSolvable_of_odd_natCard X hX
  let Fc : Subgroup A → ℕ := fun S =>
    letI : MulDistribMulAction S X := MulDistribMulAction.compHom X S.subtype
    Nat.card (fixedPointSubgroup S X)
  have hFc : ∀ S : Subgroup A, Fc S = Nat.card {x : X // ∀ g ∈ S, g • x = x} := by
    intro S
    let _ : MulDistribMulAction S X := MulDistribMulAction.compHom X S.subtype
    show Nat.card (fixedPointSubgroup S X) = _
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro h g hg
      exact h ⟨g, hg⟩
    · intro h g
      exact h g g.2
  have hFbot : Fc ⊥ = Nat.card X := by
    rw [hFc]
    refine Nat.card_congr (Equiv.subtypeUnivEquiv fun x g hg => ?_)
    rw [Subgroup.mem_bot.mp hg, one_smul]
  have hFtop : Fc ⊤ = Nat.card (fixedPointSubgroup A X) := by
    rw [hFc]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun h g => h g (Subgroup.mem_top g), fun h g _ => h g⟩)
  have hFz : ∀ a : A, Fc (Subgroup.zpowers a) =
      Nat.card (fixedPointSubgroup (Subgroup.zpowers a) X) := by
    intro a
    rw [hFc]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun h g => h g g.2, fun h g hg => h ⟨g, hg⟩⟩)
  let B : Option (Option A) → Subgroup A := fun i => i.elim ⊥ fun j => j.elim ⊤ Subgroup.zpowers
  let m : Option (Option A) → ℕ := fun i => i.elim 3 fun j => j.elim 1 fun _ => 0
  let n : Option (Option A) → ℕ := fun i => i.elim 0 fun j => j.elim 0 fun _ => 1
  have hcoeff : ∀ g : A, (∑ i, if g ∈ B i then m i else 0) =
      ∑ i, if g ∈ B i then n i else 0 := by
    intro g
    rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_option, Fintype.sum_option]
    change ((if g ∈ (⊥ : Subgroup A) then 3 else 0) + ((if g ∈ (⊤ : Subgroup A) then 1 else 0) +
        ∑ a : A, if g ∈ Subgroup.zpowers a then 0 else 0)) =
      (if g ∈ (⊥ : Subgroup A) then 0 else 0) + ((if g ∈ (⊤ : Subgroup A) then 0 else 0) +
        ∑ a : A, if g ∈ Subgroup.zpowers a then 1 else 0)
    simp only [ite_self, Finset.sum_const_zero, add_zero, zero_add, Subgroup.mem_top, ↓reduceIte,
      Subgroup.mem_bot]
    by_cases hg : g = 1
    · subst hg
      simp only [↓reduceIte, Subgroup.one_mem, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        mul_one]
      rw [← Nat.card_eq_fintype_card, hA4]
    · simp only [hg, ↓reduceIte]
      have hmem : ∀ a : A, (if g ∈ Subgroup.zpowers a then 1 else 0) = if a = g then 1 else 0 := by
        intro a
        have hiff : g ∈ Subgroup.zpowers a ↔ a = g := by
          rw [mem_zpowers_of_isKleinFour]
          constructor
          · rintro (h | h)
            · exact absurd h hg
            · exact h.symm
          · intro h
            exact Or.inr h.symm
        simp only [hiff]
      simp only [hmem, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hprod := CFSG.Wielandt.fixedPointSubgroup_product_card_eq_of_coeff_sum_eq hcop hsolv B m n
    hcoeff
  change (∏ i, Fc (B i) ^ (m i * Nat.card (B i))) = ∏ i, Fc (B i) ^ (n i * Nat.card (B i))
    at hprod
  rw [Fintype.prod_option, Fintype.prod_option, Fintype.prod_option, Fintype.prod_option] at hprod
  change Fc ⊥ ^ (3 * Nat.card (⊥ : Subgroup A)) * (Fc ⊤ ^ (1 * Nat.card (⊤ : Subgroup A)) *
      ∏ a : A, Fc (Subgroup.zpowers a) ^ (0 * Nat.card (Subgroup.zpowers a))) =
    Fc ⊥ ^ (0 * Nat.card (⊥ : Subgroup A)) * (Fc ⊤ ^ (0 * Nat.card (⊤ : Subgroup A)) *
      ∏ a : A, Fc (Subgroup.zpowers a) ^ (1 * Nat.card (Subgroup.zpowers a))) at hprod
  simp only [zero_mul, pow_zero, Finset.prod_const_one, mul_one, one_mul, Subgroup.card_bot,
    Subgroup.card_top, hFbot, hFtop, hA4] at hprod
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : A)), Subgroup.zpowers_one_eq_bot,
    Subgroup.card_bot, pow_one, hFbot] at hprod
  have hcard2 : ∀ a ∈ Finset.univ.erase (1 : A),
      Fc (Subgroup.zpowers a) ^ Nat.card (Subgroup.zpowers a) =
        Nat.card (fixedPointSubgroup (Subgroup.zpowers a) X) ^ 2 := by
    intro a ha
    have ha1 : a ≠ 1 := Finset.ne_of_mem_erase ha
    have hord : orderOf a = 2 := by
      have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        rw [pow_two]
        exact IsKleinFour.mul_self a)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ha1
      · exact h
    rw [Nat.card_zpowers, hord, hFz]
  rw [Finset.prod_congr rfl hcard2, Finset.prod_pow] at hprod
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hsq : (Nat.card X * Nat.card (fixedPointSubgroup A X) ^ 2) ^ 2 =
      (∏ a ∈ Finset.univ.erase (1 : A),
        Nat.card (fixedPointSubgroup (Subgroup.zpowers a) X)) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hXpos
    rw [← hprod]
    ring
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsq

section ULift

variable {A : Type u} {X : Type v} [Group A] [Group X] [MulDistribMulAction A X]

theorem card_fixedPointSubgroup_ulift :
    Nat.card (fixedPointSubgroup (ULift.{v} A) (ULift.{u} X)) =
      Nat.card (fixedPointSubgroup A X) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Equiv.ulift fun x => ?_)
  constructor
  · intro h a
    exact congrArg ULift.down (h (ULift.up a))
  · intro h a
    exact congrArg ULift.up (h a.down)

theorem card_fixedPointSubgroup_zpowers_ulift (a : A) :
    Nat.card (fixedPointSubgroup (Subgroup.zpowers (ULift.up.{v} a)) (ULift.{u} X)) =
      Nat.card (fixedPointSubgroup (Subgroup.zpowers a) X) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Equiv.ulift fun x => ?_)
  rw [SolvableHall.mem_fixedPointSubgroup_zpowers_iff,
    SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
  constructor
  · intro h
    exact congrArg ULift.down h
  · intro h
    exact congrArg ULift.up h

end ULift

theorem card_fixedPointSubgroup_subtype {B X : Type*} [Group B] [Group X]
    [MulDistribMulAction B X] (Y : Subgroup X) [MulDistribMulAction B Y]
    (hY : ∀ (b : B) (y : Y), ((b • y : Y) : X) = b • (y : X)) :
    Nat.card (fixedPointSubgroup B Y) = Nat.card (Y ⊓ fixedPointSubgroup B X : Subgroup X) := by
  refine Nat.card_congr
    { toFun := fun y =>
        ⟨(y : Y), (y : Y).2, fun b => by rw [← hY]; exact congrArg Subtype.val (y.2 b)⟩
      invFun := fun x => ⟨⟨x, x.2.1⟩, fun b => Subtype.ext (by rw [hY]; exact x.2.2 b)⟩
      left_inv := fun y => rfl
      right_inv := fun x => rfl }

end CFSG.GroupTheory
