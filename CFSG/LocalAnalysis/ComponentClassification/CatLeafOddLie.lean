module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_of_lieModel_psl_two_eight (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : LieModel X .PSL 2 2 3) : Nat.card X = 504 := by
  have hadm : StatedLieAdmissible .PSL 2 2 3 := by
    refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
  obtain ⟨-, hord, -⟩ := hO X .PSL 2 2 3 hadm h
  have h1 : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
  have h2 : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
  rw [h1, h2, mul_one] at hord
  exact hord

theorem not_held_not_L34_of_properFixedComponent_oddLie (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) :
    ¬ GrSLit.IsHeldType (P ⧸ Open.fusionZStar P) ∧ ¬ GrSLit.IsL34Type (P ⧸ Open.fusionZStar P) :=
  by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  have hcard : Nat.card (P ⧸ Open.fusionZStar P) = Nat.card (L ⧸ center L) :=
    Nat.card_congr eZ.toEquiv
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨eH⟩
      apply lieModel_card_ne_held hO hadm' hm'
      rw [← hcard, Nat.card_congr eH.toEquiv, Sporadic.He.card_He]
    · intro hL
      apply lieModel_odd_card_ne_L34 hO hp2 hadm' hm'
      rw [← hcard, card_of_isL34Type hL]
  · have h504 := card_of_lieModel_psl_two_eight hO h8
    have hle : Nat.card (L ⧸ center L) ≤ 504 := by
      rw [← h504]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    refine ⟨?_, ?_⟩
    · rintro ⟨eH⟩
      rw [← hcard, Nat.card_congr eH.toEquiv, Sporadic.He.card_He] at hle
      norm_num at hle
    · intro hL
      rw [← hcard, card_of_isL34Type hL] at hle
      norm_num at hle

end CFSG.ComponentClassification.CatLeaf
