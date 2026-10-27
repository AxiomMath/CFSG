module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneSolvable
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineDegree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffinePrimePower

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

open CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
open CFSG.ProperTwoGeneratedCore.LocalCriterionAffineOddPair

variable {Ω : Type*} [Finite Ω]

theorem solvable_two_pretransitive_regular_elementary_subgroup
    (F : Subgroup (Equiv.Perm Ω))
    (htwo : MulAction.IsMultiplyPretransitive F Ω 2)
    (hdegree : 2 ≤ Nat.card Ω) (hsolvable : Group.IsSolvable F) :
    ∃ (p : ℕ) (Q : Subgroup F), p.Prime ∧ Q ≠ ⊥ ∧ Q.Normal ∧
      IsElementaryAbelian p Q ∧ RegularOnEntire F Q ∧
      Nat.card Ω = Nat.card Q ∧ IsPrimePow (Nat.card Ω) := by
  let : MulAction.IsMultiplyPretransitive F Ω 2 := htwo
  let : MulAction.IsPretransitive F Ω := MulAction.isPretransitive_of_is_two_pretransitive
  let : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
  have hFcard : 2 ≤ Nat.card F := hdegree.trans
    (Nat.le_of_dvd Nat.card_pos (degree_dvd_group_order_of_pretransitive
      (inferInstance : MulAction.IsPretransitive F Ω) a))
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hRsolvable : Group.IsSolvable (⊤ : Subgroup F) :=
    Group.isSolvable_of_isSolvable_injective (⊤ : Subgroup F).subtype_injective
  obtain ⟨p, Q, hp, hQne, hQnormal, _, hQelem, _, _, _, _, hQreg⟩ :=
    solvable_normal_primitive_regular_subgroup hdegree a
      (two_pretransitive_point_stabilizer_isCoatom htwo hdegree a)
      (⊤ : Subgroup F) inferInstance top_ne_bot hRsolvable
  let : IsElementaryAbelian p Q := hQelem
  have hreg : RegularOnEntire F Q := hQreg
  exact ⟨p, Q, hp, hQne, hQnormal, hQelem, hreg,
    (regular_card_eq_degree F Q hreg a).symm,
    regular_elementary_degree_isPrimePow F p hp Q hreg hdegree⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
