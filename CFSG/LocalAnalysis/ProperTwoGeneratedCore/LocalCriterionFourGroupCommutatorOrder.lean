module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorCoefficient
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorCoefficient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.Algebra.Module.ULift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG
open scoped IsMulCommutative

universe u v

attribute [local instance] Classical.propDecidable

variable {A : Type u} [Group A]
variable {I : Type v} [Group I] [MulDistribMulAction A I]

theorem fixedPointSubgroup_zpowers_eq_actorFixed (a : A) :
    (letI := MulDistribMulAction.compHom I (Subgroup.zpowers a).subtype
     fixedPointSubgroup (Subgroup.zpowers a) I) = actorFixedSubgroup a := by
  ext x
  constructor
  · intro hx
    exact hx ⟨a, Subgroup.mem_zpowers a⟩
  · intro hx y
    exact smul_eq_self_of_mem_zpowers y.property hx

theorem fixedPointSubgroup_top_eq :
    (letI := MulDistribMulAction.compHom I (⊤ : Subgroup A).subtype
     fixedPointSubgroup (⊤ : Subgroup A) I) = fixedPointSubgroup A I := by
  ext x
  exact ⟨fun h a => h ⟨a, trivial⟩, fun h a => h a.val⟩

theorem fixedPointSubgroup_bot_eq :
    (letI := MulDistribMulAction.compHom I (⊥ : Subgroup A).subtype
     fixedPointSubgroup (⊥ : Subgroup A) I) = ⊤ := by
  ext x
  simp only [Subgroup.mem_top, iff_true]
  intro a
  have ha : a.val = 1 := a.property
  change a.val • x = x
  rw [ha, one_smul]

theorem four_group_order_identity_same_universe
    [Finite A] {V : Type u} [Group V] [Finite V] [MulDistribMulAction A V]
    [IsKleinFour A] (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card V)) :
    Nat.card V * Nat.card (fixedPointSubgroup A V) ^ 2 =
      Nat.card (actorFixedSubgroup (I := V) a) *
        Nat.card (actorFixedSubgroup (I := V) b) *
          Nat.card (actorFixedSubgroup (I := V) (a * b)) := by
  classical
  have hcop : Nat.Coprime (Nat.card V) (Nat.card A) := by
    rw [IsKleinFour.card_four (G := A)]
    simpa using hodd.coprime_two_right.pow_right 2
  let e : ULift.{u} (Fin 5) ≃ Fin 5 := Equiv.ulift
  have hcoeff (x : A) :
      (∑ i : ULift.{u} (Fin 5), if x ∈ fourGroupCoefficientSubgroup a b i.down then
        fourGroupCoefficientLeft i.down else 0) =
      ∑ i : ULift.{u} (Fin 5), if x ∈ fourGroupCoefficientSubgroup a b i.down then
        fourGroupCoefficientRight i.down else 0 := by
    calc
      _ = ∑ i : Fin 5, if x ∈ fourGroupCoefficientSubgroup a b i then
        fourGroupCoefficientLeft i else 0 := e.sum_comp _
      _ = _ := fourGroupCoefficient_relation a b ha hb hab x
      _ = _ := (e.sum_comp _).symm
  have hprod := Wielandt.fixedPointSubgroup_product_card_eq_of_coeff_sum_eq
    (G := A) (V := V) (ι := ULift.{u} (Fin 5)) hcop (CFSG.FeitThompson.isSolvable_of_odd_natCard V hodd)
    (fun i => fourGroupCoefficientSubgroup a b i.down)
    (fun i => fourGroupCoefficientLeft i.down) (fun i => fourGroupCoefficientRight i.down)
    hcoeff
  have hprod' :
      (∏ i : Fin 5,
        let : MulDistribMulAction (fourGroupCoefficientSubgroup a b i) V :=
          MulDistribMulAction.compHom V (fourGroupCoefficientSubgroup a b i).subtype
        Nat.card (fixedPointSubgroup (fourGroupCoefficientSubgroup a b i) V) ^
          (fourGroupCoefficientLeft i * Nat.card (fourGroupCoefficientSubgroup a b i))) =
      ∏ i : Fin 5,
        let : MulDistribMulAction (fourGroupCoefficientSubgroup a b i) V :=
          MulDistribMulAction.compHom V (fourGroupCoefficientSubgroup a b i).subtype
        Nat.card (fixedPointSubgroup (fourGroupCoefficientSubgroup a b i) V) ^
          (fourGroupCoefficientRight i * Nat.card (fourGroupCoefficientSubgroup a b i)) := by
    calc
      _ = _ := (e.prod_comp _).symm
      _ = _ := hprod
      _ = _ := e.prod_comp _
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hca : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime_iff.2 ⟨by
      simpa only [pow_two] using IsKleinFour.mul_self a, ha⟩
  have hcb : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime_iff.2 ⟨by
      simpa only [pow_two] using IsKleinFour.mul_self b, hb⟩
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hab ((mul_eq_one_iff_eq_inv.mp h).trans (IsKleinFour.inv_eq_self b))
  have hcab : Nat.card (Subgroup.zpowers (a * b)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime_iff.2 ⟨by
      simpa only [pow_two] using IsKleinFour.mul_self (a * b), hab1⟩
  simp only [Fin.prod_univ_five] at hprod'
  dsimp +instances [fourGroupCoefficientSubgroup, fourGroupCoefficientLeft,
    fourGroupCoefficientRight] at hprod'
  simp only [Nat.zero_mul, Nat.one_mul, pow_zero, Nat.mul_one, Nat.one_mul,
    Subgroup.card_top, Subgroup.card_bot, IsKleinFour.card_four (G := A)] at hprod'
  rw [hca, hcb, hcab] at hprod'
  rw [fixedPointSubgroup_top_eq (A := A) (I := V),
    fixedPointSubgroup_bot_eq (A := A) (I := V),
    fixedPointSubgroup_zpowers_eq_actorFixed (I := V) a,
    fixedPointSubgroup_zpowers_eq_actorFixed (I := V) b,
    fixedPointSubgroup_zpowers_eq_actorFixed (I := V) (a * b),
    Subgroup.card_top] at hprod'
  have hsquare :
      (Nat.card V * Nat.card (fixedPointSubgroup A V) ^ 2) ^ 2 =
      (Nat.card (actorFixedSubgroup (I := V) a) *
        Nat.card (actorFixedSubgroup (I := V) b) *
          Nat.card (actorFixedSubgroup (I := V) (a * b))) ^ 2 := by
    calc
      _ = Nat.card (fixedPointSubgroup A V) ^ 4 * Nat.card V ^ 2 := by ring
      _ = _ := hprod'
      _ = _ := by ring
  exact Nat.mul_self_inj.mp (by simpa only [pow_two] using hsquare)

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
