module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Generation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X]

theorem not_isSimpleGroup_perm_fin {m : ℕ} (hm : 3 ≤ m) : ¬ IsSimpleGroup (Perm (Fin m)) := by
  intro hs
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin m)) with h | h
  · have h1 : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [h, Subgroup.card_bot] at h1
    have h2 : (3 : ℕ).factorial ≤ m.factorial := Nat.factorial_le hm
    have h3 : (3 : ℕ).factorial = 6 := rfl
    omega
  · have h1 : (alternatingGroup (Fin m)).index = 2 := alternatingGroup.index_eq_two
    rw [h, Subgroup.index_top] at h1
    omega

end CFSG.ComponentClassification.Sol78
