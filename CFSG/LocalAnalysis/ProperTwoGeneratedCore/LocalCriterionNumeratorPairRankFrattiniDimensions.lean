module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniFixed
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorLift

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u v

theorem elementary_subgroup {p : ℕ} {V : Type v} [Group V]
    [IsElementaryAbelian p V] (K : Subgroup V) : IsElementaryAbelian p K := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro x
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p V) x.val

theorem elementary_card_eq_pow_finrank {p : ℕ} [Fact p.Prime]
    {V : Type v} [Group V] [Finite V] [IsElementaryAbelian p V] :
    Nat.card V = p ^ Module.finrank (ZMod p) (Additive V) := by
  let : Finite (Additive V) := inferInstanceAs (Finite V)
  let : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
  change Nat.card (Additive V) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem elementary_finrank_le_of_card_le {p n : ℕ} [Fact p.Prime]
    {V : Type v} [Group V] [Finite V] [IsElementaryAbelian p V]
    (hcard : Nat.card V ≤ p ^ n) :
    Module.finrank (ZMod p) (Additive V) ≤ n := by
  rw [elementary_card_eq_pow_finrank (p := p)] at hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard

theorem frattini_cyclic_fixed_finrank
    {A : Type u} [Group A] [Finite A]
    {P : Type v} [Group P] [Finite P] [MulDistribMulAction A P]
    {p : ℕ} [Fact p.Prime]
    (hP : IsPGroup p P) (hpodd : Odd p) (w t : A) (hw : w ^ 2 = 1)
    (hwt : Commute w t)
    (ht : let := frattiniQuotientAction (A := A) (P := P)
      ∀ x : P ⧸ frattini P, t • x = x⁻¹)
    (hcyclic : IsCyclic (actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w))) :
    let := frattiniQuotientAction (A := A) (P := P)
    let : IsElementaryAbelian p (P ⧸ frattini P) :=
      (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
    let : IsElementaryAbelian p (actorFixedSubgroup (I := P ⧸ frattini P) w) :=
      elementary_subgroup (actorFixedSubgroup (I := P ⧸ frattini P) w)
    Module.finrank (ZMod p) (Additive (actorFixedSubgroup (I := P ⧸ frattini P) w)) ≤ 1 := by
  let := frattiniQuotientAction (A := A) (P := P)
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  let : IsElementaryAbelian p (actorFixedSubgroup (I := P ⧸ frattini P) w) :=
    elementary_subgroup (actorFixedSubgroup (I := P ⧸ frattini P) w)
  apply elementary_finrank_le_of_card_le
  simpa only [pow_one] using (frattini_cyclic_fixed_card hP hpodd w t hw hwt ht hcyclic).2.2

theorem klein_four_fixed_card_bound
    {W : Type u} [Group W] [Finite W] [IsKleinFour W]
    {V : Type v} [Group V] [Finite V] [MulDistribMulAction W V]
    (hodd : Odd (Nat.card V)) (p : ℕ)
    (hfixed : ∀ w : W, w ≠ 1 → Nat.card (actorFixedSubgroup (I := V) w) ≤ p) :
    Nat.card V ≤ p ^ 3 := by
  classical
  let : Fintype W := Fintype.ofFinite W
  have hthree : 2 < Fintype.card W := by rw [IsKleinFour.card_four']; decide
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hthree
  have hpair : ∃ x y : W, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
    by_cases ha : a = 1
    · exact ⟨b, c, fun hb => hab (ha.trans hb.symm),
        fun hc => hac (ha.trans hc.symm), hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, fun hc => hbc (hb.trans hc.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := hpair
  have hprod : x * y ≠ 1 := by
    intro h
    have heq := mul_eq_one_iff_eq_inv.mp h
    exact hxy (heq.trans (IsKleinFour.inv_eq_self y))
  have hidentity := four_group_order_identity x y hx hy hxy hodd
  have hcommon : 0 < Nat.card (fixedPointSubgroup W V) ^ 2 :=
    Nat.pow_pos (Nat.card_pos (α := fixedPointSubgroup W V))
  calc
    Nat.card V ≤ Nat.card V * Nat.card (fixedPointSubgroup W V) ^ 2 :=
      Nat.le_mul_of_pos_right _ hcommon
    _ = Nat.card (actorFixedSubgroup (I := V) x) *
        Nat.card (actorFixedSubgroup (I := V) y) *
          Nat.card (actorFixedSubgroup (I := V) (x * y)) := hidentity
    _ ≤ p * p * p := Nat.mul_le_mul (Nat.mul_le_mul (hfixed x hx) (hfixed y hy))
      (hfixed (x * y) hprod)
    _ = p ^ 3 := by ring

theorem klein_four_elementary_finrank_bound
    {W : Type u} [Group W] [Finite W] [IsKleinFour W]
    {p : ℕ} [Fact p.Prime]
    {V : Type v} [Group V] [Finite V] [IsElementaryAbelian p V]
    [MulDistribMulAction W V] (hpodd : Odd p)
    (hfixed : ∀ w : W, w ≠ 1 → Nat.card (actorFixedSubgroup (I := V) w) ≤ p) :
    Nat.card V ≤ p ^ 3 ∧ Module.finrank (ZMod p) (Additive V) ≤ 3 := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p V).exists_card_eq
  have hodd : Odd (Nat.card V) := by rw [hn]; exact hpodd.pow
  have hcard := klein_four_fixed_card_bound hodd p hfixed
  exact ⟨hcard, elementary_finrank_le_of_card_le hcard⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
