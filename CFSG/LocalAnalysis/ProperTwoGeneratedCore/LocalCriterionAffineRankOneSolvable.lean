module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne

open scoped IsMulCommutative

universe u v

theorem solvable_normal_primitive_regular_subgroup
    {F : Type u} [Group F] [Finite F]
    {Λ : Type v} [MulAction F Λ] [Finite Λ]
    [MulAction.IsPretransitive F Λ] [FaithfulSMul F Λ]
    (hdegree : 2 ≤ Nat.card Λ) (a : Λ)
    (hmax : IsCoatom (MulAction.stabilizer F a))
    (R : Subgroup F) (hRnormal : R.Normal) (hRne : R ≠ ⊥)
    (hRsolvable : Group.IsSolvable R) :
    ∃ (ℓ : ℕ) (Q : Subgroup F),
      ℓ.Prime ∧ Q ≠ ⊥ ∧ Q.Normal ∧ Q ≤ R ∧ IsElementaryAbelian ℓ Q ∧
      Q.IsComplement' (MulAction.stabilizer F a) ∧
      Q ⊔ MulAction.stabilizer F a = ⊤ ∧
      Q ⊓ MulAction.stabilizer F a = ⊥ ∧
      MulAction.stabilizer F a ⊓ Subgroup.centralizer (Q : Set F) = ⊥ ∧
      ∀ x y : Λ, ∃! q : Q, q • x = y := by
  classical
  let : Nontrivial Λ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨Q, hQnormal, hQR, hQne, hQmin⟩ := exists_minimal_normal_le R hRnormal hRne
  let : Q.Normal := hQnormal
  let : IsMinimalNormal Q := ⟨fun K hKnormal hKQ => by
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · exact Or.inr (hQmin K hKnormal hKQ hK)⟩
  let : Group.IsSolvable R := hRsolvable
  let : Group.IsSolvable Q :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hQR)
  obtain ⟨ℓ, hℓ, hQelementary⟩ := minimalNormal_solvable_exists_isElementaryAbelian Q
  let : IsElementaryAbelian ℓ Q := hQelementary
  obtain ⟨hcompl, hprod, hinter, hcentralizer, hregular⟩ :=
    abelian_normal_primitive_complement a hmax Q hQne
  exact ⟨ℓ, Q, hℓ, hQne, hQnormal, hQR, hQelementary,
    hcompl, hprod, hinter, hcentralizer, hregular⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
