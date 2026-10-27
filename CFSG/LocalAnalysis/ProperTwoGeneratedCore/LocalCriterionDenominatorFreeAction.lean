module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped BigOperators

theorem free_action_card_dvd {A X : Type*} [Group A] [Finite A]
    [MulAction A X] [Finite X]
    (hfree : ∀ a : A, ∀ x : X, a • x = x → a = 1) :
    Nat.card A ∣ Nat.card X := by
  classical
  let : IsCancelSMul A X := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  let : Fintype A := Fintype.ofFinite A
  let : Fintype X := Fintype.ofFinite X
  let : Fintype (MulAction.orbitRel.Quotient A X) := Fintype.ofFinite _
  let : ∀ x : X, Fintype (MulAction.stabilizer A x) := fun _ => Fintype.ofFinite _
  have hcard := MulAction.card_eq_sum_card_group_div_card_stabilizer A X
  have hstab : ∀ x : X, Fintype.card (MulAction.stabilizer A x) = 1 := by
    intro x
    rw [← Nat.card_eq_fintype_card, IsCancelSMul.stabilizer_eq_bot, Subgroup.card_bot]
  simp only [hstab, Nat.div_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [hcard]
  exact dvd_mul_left _ _

variable {G : Type*} [Group G]

theorem centralizer_preserves_elementFixedSet (H : Subgroup G) (v g : G)
    (hg : g ∈ Subgroup.centralizer ({v} : Set G))
    (a : pointRightCosetSpace H) (ha : a ∈ elementFixedSet H v) :
    pointRightCosetMul H a g ∈ elementFixedSet H v := by
  have hcomm : g * v = v * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  change pointRightCosetMul H (pointRightCosetMul H a g) v = pointRightCosetMul H a g
  rw [pointRightCosetMul_mul, hcomm, ← pointRightCosetMul_mul, ha]

@[expose, instance_reducible] def productFixedSetAction (H L : Subgroup G) (v : G)
    (hLC : L ≤ Subgroup.centralizer ({v} : Set G)) :
    MulAction L (elementFixedSet H v) :=
  pointInvariantSetInverseRightAction H L (elementFixedSet H v)
    (fun g hg a ha => centralizer_preserves_elementFixedSet H v g (hLC hg) a ha)

theorem denominator_card_dvd_entire_fixedSet [Finite G] (H W : Subgroup G) (v : G)
    (hWC : W ≤ Subgroup.centralizer ({v} : Set G))
    (a b : pointRightCosetSpace H)
    (hdisjoint : Disjoint (elementFixedSet H v) ({a, b} : Set (pointRightCosetSpace H)))
    (hfix : ∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {a, b}) :
    Nat.card W ∣ Nat.card (elementFixedSet H v) := by
  let := productFixedSetAction H W v hWC
  apply free_action_card_dvd
  intro x p hxp
  by_contra hx
  have hxinv : ((x : G)⁻¹) ≠ 1 := by
    intro h
    apply hx
    exact Subtype.ext (inv_eq_one.mp h)
  have hpfix : p.val ∈ elementFixedSet H ((x : G)⁻¹) :=
    congrArg Subtype.val hxp
  rw [hfix _ (W.inv_mem x.property) hxinv] at hpfix
  exact Set.disjoint_left.mp hdisjoint p.property hpfix

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
