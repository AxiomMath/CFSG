module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniDimensions
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u v

variable {A : Type u} [Group A]
variable {I : Type v} [Group I] [MulDistribMulAction A I]

theorem invariant_fixed_commutator_map_le
    (P : Subgroup I) [CFSG.IsInvariant A I P] (w t : A) :
    (actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w)).map P.subtype ≤
      actorCommutatorSubgroup t (actorFixedSubgroup (I := I) w) := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (actorCommutatorSubgroup_le t _ _).2
  intro x hx
  change (x : I)⁻¹ * (t • (x : I)) ∈
    actorCommutatorSubgroup t (actorFixedSubgroup (I := I) w)
  apply actorCommutatorSubgroup_generator_mem
  exact congrArg Subtype.val hx

theorem invariant_fixed_commutator_cyclic
    (P : Subgroup I) [CFSG.IsInvariant A I P] (w t : A)
    (hcyclic : IsCyclic (actorCommutatorSubgroup t (actorFixedSubgroup (I := I) w))) :
    IsCyclic (actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w)) := by
  let K := actorCommutatorSubgroup t (actorFixedSubgroup (I := P) w)
  let := hcyclic
  let : IsCyclic (K.map P.subtype) :=
    Subgroup.isCyclic_of_le (invariant_fixed_commutator_map_le P w t)
  exact isCyclic_of_injective (P.subtype.subgroupMap K)
    (P.subtype.subgroupMap_injective K P.subtype_injective)

theorem invariant_frattini_four_group_bounds [Finite A] [Finite I]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (P : Subgroup I) [CFSG.IsInvariant A I P] (hP : IsPGroup p P)
    (W : Subgroup A) [IsKleinFour W] (t : A)
    (hwt : ∀ w : W, Commute (w : A) t)
    (ht : let := frattiniQuotientAction (A := A) (P := P)
      ∀ x : P ⧸ frattini P, t • x = x⁻¹)
    (hcyclic : ∀ w : W, w ≠ 1 →
      IsCyclic (actorCommutatorSubgroup t (actorFixedSubgroup (I := I) (w : A)))) :
    let := frattiniQuotientAction (A := A) (P := P)
    let : MulDistribMulAction W (P ⧸ frattini P) :=
      MulDistribMulAction.compHom (P ⧸ frattini P) W.subtype
    let : IsElementaryAbelian p (P ⧸ frattini P) :=
      (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
    (∀ w : W, w ≠ 1 →
      let : IsElementaryAbelian p (actorFixedSubgroup (I := P ⧸ frattini P) w) :=
        elementary_subgroup (actorFixedSubgroup (I := P ⧸ frattini P) w)
      IsCyclic (actorFixedSubgroup (I := P ⧸ frattini P) w) ∧
        Nat.card (actorFixedSubgroup (I := P ⧸ frattini P) w) ≤ p ∧
          Module.finrank (ZMod p)
            (Additive (actorFixedSubgroup (I := P ⧸ frattini P) w)) ≤ 1) ∧
      Nat.card (P ⧸ frattini P) ≤ p ^ 3 ∧
        Module.finrank (ZMod p) (Additive (P ⧸ frattini P)) ≤ 3 := by
  let := frattiniQuotientAction (A := A) (P := P)
  let : MulDistribMulAction W (P ⧸ frattini P) :=
    MulDistribMulAction.compHom (P ⧸ frattini P) W.subtype
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    (GroupTheory.frattini_elementary_quotient hP).2.2.2.1
  have hlocal (w : W) (hw : w ≠ 1) :
      IsCyclic (actorFixedSubgroup (I := P ⧸ frattini P) w) ∧
        Nat.card (actorFixedSubgroup (I := P ⧸ frattini P) w) ≤ p := by
    have hwsq : (w : A) ^ 2 = 1 := by
      simpa only [pow_two, Subgroup.coe_mul, Subgroup.coe_one] using
        congrArg Subtype.val (IsKleinFour.mul_self w)
    have hc := invariant_fixed_commutator_cyclic P (w : A) t (hcyclic w hw)
    have hfixed := frattini_cyclic_fixed_card hP hpodd (w : A) t hwsq (hwt w) ht hc
    exact ⟨hfixed.1, hfixed.2.2⟩
  change _ ∧ _ ∧ _
  refine ⟨?_, ?_⟩
  · intro w hw
    let : IsElementaryAbelian p (actorFixedSubgroup (I := P ⧸ frattini P) w) :=
      elementary_subgroup (actorFixedSubgroup (I := P ⧸ frattini P) w)
    obtain ⟨hc, hcard⟩ := hlocal w hw
    exact ⟨hc, hcard, elementary_finrank_le_of_card_le (n := 1)
      (by simpa only [pow_one] using hcard)⟩
  · exact klein_four_elementary_finrank_bound hpodd (fun w hw => (hlocal w hw).2)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
