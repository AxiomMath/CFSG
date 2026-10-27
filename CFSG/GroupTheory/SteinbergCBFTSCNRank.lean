module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

omit [Finite P] in
theorem exists_isElementaryAbelian_of_three_le_pRank {B : Subgroup P}
    (hB : 3 ≤ CFSG.pRank p B) :
    ∃ E : Subgroup B, CFSG.IsElementaryAbelian p E ∧ p ^ 3 ≤ Nat.card E := by
  by_contra h
  have h' : ∀ E : Subgroup B, CFSG.IsElementaryAbelian p E → Nat.card E < p ^ 3 :=
    fun E hE => lt_of_not_ge fun h3 => h ⟨E, hE, h3⟩
  have hne :
      {r : ℕ | ∃ E : Subgroup B, CFSG.IsElementaryAbelian p E ∧ Nat.card E = p ^ r}.Nonempty :=
    ⟨0, ⊥, { toIsMulCommutative := ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
             exponent_dvd_p := by rw [Monoid.exp_eq_one_of_subsingleton]; exact one_dvd p },
      by rw [card_bot, pow_zero]⟩
  have hle : CFSG.pRank p B ≤ 2 := by
    refine csSup_le hne ?_
    rintro r ⟨E, hE, hcard⟩
    by_contra hr
    have := h' E hE
    rw [hcard] at this
    exact absurd (Nat.pow_lt_pow_iff_right hp.out.one_lt |>.1 this) (by omega)
  omega

end CFSG.GroupTheory.FT63ChII
