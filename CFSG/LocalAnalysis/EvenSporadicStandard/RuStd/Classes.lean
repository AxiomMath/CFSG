module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.SignCoset

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup

section Group

variable {Y : Type} [Group Y]

theorem orderOf_eq_of_isConj' {a l : Y} (h : IsConj a l) : orderOf l = orderOf a := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (SemiconjBy.orderOf_eq c (show SemiconjBy c a (c * a * c⁻¹) by
    simp [SemiconjBy, mul_assoc])).symm

theorem card_centralizer_of_isConj {a l : Y} (h : IsConj a l) :
    Nat.card (centralizer ({l} : Set Y)) = Nat.card (centralizer ({a} : Set Y)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun x => ?_).symm
  have key : ∀ x : Y, (c * x * c⁻¹) * (c * a * c⁻¹) = c * (x * a) * c⁻¹ := fun x => by group
  have key2 : ∀ x : Y, (c * a * c⁻¹) * (c * x * c⁻¹) = c * (a * x) * c⁻¹ := fun x => by group
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  show _ ↔ (c * x * c⁻¹) * (c * a * c⁻¹) = (c * a * c⁻¹) * (c * x * c⁻¹)
  rw [key, key2]
  constructor
  · intro hx
    rw [hx]
  · intro hx
    exact mul_left_cancel (mul_right_cancel hx)

theorem card_class_mul_card_centralizer (a : Y) :
    Nat.card {y : Y // IsConj a y} * Nat.card (centralizer ({a} : Set Y)) = Nat.card Y := by
  have h := card_conjTo_eq' (⊤ : Subgroup Y) a
  have e1 : Nat.card {t : Y // t⁻¹ * a * t ∈ (⊤ : Subgroup Y)} = Nat.card Y :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun t => Subgroup.mem_top _)
  have e2 : Nat.card {y : Y // y ∈ (⊤ : Subgroup Y) ∧ IsConj a y} =
      Nat.card {y : Y // IsConj a y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)
  rw [e1, e2] at h
  exact h.symm

variable [Finite Y]

omit [Finite Y] in
theorem RuFacts.card_classB (hF : RuFacts Y) {b : Y}
    (hbB : Nat.card (centralizer ({b} : Set Y)) = 116480) :
    Nat.card {y : Y // IsConj b y} = 1252800 := by
  have h := card_class_mul_card_centralizer b
  rw [hbB, hF.card_eq] at h
  omega

omit [Finite Y] in
theorem RuFacts.ncard_involB (hF : RuFacts Y) {b : Y} (hb2 : orderOf b = 2)
    (hbB : Nat.card (centralizer ({b} : Set Y)) = 116480) :
    {l : Y | orderOf l = 2 ∧ Nat.card (centralizer ({l} : Set Y)) = 116480}.ncard = 1252800 := by
  have hset : {l : Y | orderOf l = 2 ∧ Nat.card (centralizer ({l} : Set Y)) = 116480} =
      {y : Y | IsConj b y} := by
    ext l
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hl2, hlB⟩
      exact hF.isConj_B b l hb2 hl2 hbB hlB
    · intro h
      exact ⟨(orderOf_eq_of_isConj' h).trans hb2,
        (card_centralizer_of_isConj h).trans hbB⟩
  rw [hset, ← Nat.card_coe_set_eq]
  exact hF.card_classB hbB

end Group

section Coset

variable {G : Type} [Group G] [Finite G]

theorem card_quot_eq_fixed_add_moved (K : Subgroup G) (z : G) :
    Nat.card (G ⧸ K) = Nat.card {q : G ⧸ K // z • q = q} + Nat.card {q : G ⧸ K // z • q ≠ q} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl (fun q : G ⧸ K => z • q = q)).symm

omit [Finite G] in
theorem card_fixed_mul_card' (K : Subgroup G) (z : G) :
    Nat.card {q : G ⧸ K // z • q = q} * Nat.card K =
      {y : G | y ∈ K ∧ IsConj z y}.ncard * Nat.card (centralizer ({z} : Set G)) := by
  rw [← Nat.card_coe_set_eq]
  exact card_fixed_mul_card K z

end Coset

end CFSG.EvenSporadicStandard.RuStd
