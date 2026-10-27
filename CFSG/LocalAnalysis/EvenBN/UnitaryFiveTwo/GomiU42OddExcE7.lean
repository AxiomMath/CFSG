module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExc
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcCent
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcUntw

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.false_of_oddLie_F4E8
    (h : GomiU42Data X J D E a) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t = .F4 ∨ t = .E8) (hD : ChevalleyExceptionalModel ↥D t p f) : False := by
  obtain ⟨α, hα2, hα1, hdvd⟩ := h.exists_involution_aut
  have hord : ∀ τ' : Tag, (τ' = .F4 ∨ τ' = .E8) →
      StatedLieAdmissible t 0 p f → UntwistedChevalleyModel ↥D τ' (p ^ f) → False := by
    rintro τ' hτ' ⟨-, hf, -⟩ ⟨F, _, _, hF, ⟨e⟩⟩
    let ψ : ↥D ≃* adjointGroup τ' F :=
      e.trans ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field τ' F)).trans
        QuotientGroup.quotientBot)
    refine gomi_untwisted_F4E8_false hτ' hp hp2 hf hF (MulAut.congr ψ α) ?_ ?_ ?_
    · exact fun h1 => hα1 ((MulAut.congr ψ).injective (h1.trans (map_one _).symm))
    · rw [← map_pow, hα2, map_one]
    · rw [gomi_card_eqLocus_congr ψ α]
      exact hdvd
  rcases ht with rfl | rfl
  · exact hord .F4 (Or.inl rfl) hD.1 hD.2
  · exact hord .E8 (Or.inr rfl) hD.1 hD.2

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
