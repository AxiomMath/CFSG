module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

theorem isQuasisimple_or_isSolvable_orthLeviBlock (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (j : Fin s ⊕ Unit) : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j) ∨
      Group.IsSolvable ↥(orthLeviBlock K r d b c j) := by
  rcases j with l | u
  · change CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range ∨
      Group.IsSolvable ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range
    rcases isQuasisimple_or_isSolvable_specialLinear (K := K) (d l.succ - d l.castSucc) with h | h
    · exact Or.inl (isQuasisimple_of_mulEquiv (slEquivToGLRange _) h)
    · exact Or.inr (Group.isSolvable_of_surjective
        (f := (slEquivToGLRange (K := K) (d l.succ - d l.castSucc)).toMonoidHom)
        (slEquivToGLRange _).surjective)
  · exact isQuasisimple_or_isSolvable_orthResDer hirr _

theorem card_orthLeviBlock_quotient_center_mem (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (j : Fin s ⊕ Unit) (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j)) :
    Nat.card (↥(orthLeviBlock K r d b c j) ⧸ Subgroup.center ↥(orthLeviBlock K r d b c j)) ∈
      orthMinusBlockOrders (Nat.card K) := by
  obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  rcases j with l | u
  · change CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range at hq
    change Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range ⧸
      Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range) ∈ _
    have h2 := two_le_of_isQuasisimple_specialLinear
      (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq)
    exact Or.inl ⟨_, h2, card_range_toGL_quotient_center (by omega)⟩
  · obtain ⟨hm, -, h⟩ := card_orthResDer_quotient_center hK hirr hq
    exact Or.inr ⟨r - d (Fin.last s) + 1, by omega, by rw [hK]; exact h⟩

theorem orthLeviBlock_card_of_sixty (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (j : Fin s ⊕ Unit) (hq : CFSG.Open.IsQuasisimple ↥(orthLeviBlock K r d b c j))
    (h60 : Nat.card (↥(orthLeviBlock K r d b c j) ⧸
      Subgroup.center ↥(orthLeviBlock K r d b c j)) = 60) :
    Nat.card ↥(orthLeviBlock K r d b c j) = 60 := by
  obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  rcases j with l | u
  · exact card_specialLinear_range_of_sixty hK hq h60
  · exact card_orthResDer_of_sixty hirr hq h60

theorem hasLeviBlocks_orthParab (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    HasLeviBlocks ↥(orthParab r (minusTailForm K b c) d) (orthMinusBlockOrders (Nat.card K)) :=
  HasLeviBlocks.of_index (orthLeviBlock K r d b c) (orthLeviHom b c hd)
    (isPGroup_ker_orthLeviHom hd)
    (pi_orthLeviBlock_le_range hd hr (commutator_orthogonalGroup_quadTail_minus hr hirr))
    (commutator_range_orthLeviHom_le hd) (isQuasisimple_or_isSolvable_orthLeviBlock hirr)
    (card_orthLeviBlock_quotient_center_mem hirr)

end CFSG.AGLEmbedding.LeviBlock
