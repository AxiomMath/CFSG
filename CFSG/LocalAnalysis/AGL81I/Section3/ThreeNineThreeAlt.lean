module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberAlt
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeAltPerm
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeSmall
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Equiv Equiv.Perm
open CFSG.LocalAnalysis.AGL81I.Section3.AltPerm

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_alt_three (h : ThreeNineHyp K E D X₁ 3 d) {n : ℕ}
    (hn : n = 9 ∨ n = 10 ∨ n = 11) (φ : ↥K ≃* alternatingGroup (Fin n)) : False :=
  false_of_threeNineHyp_alt_of_perm h (by omega) (by omega) φ
    fun _ _ hRp hRc hRcomm hRexp hRG _ hσc hσd hσG hσG' => by
      rcases hn with hn | hn
      · exact alternatingGroup_le_nine h.d_prime h.d_ne (by rw [Fintype.card_fin, hn]) hRp hRc
          hRcomm hRexp hRG hσc hσd hσG hσG'
      · exact alternatingGroup_le_ten_eleven h.d_prime h.d_ne_two h.d_ne
          (by rw [Fintype.card_fin]; exact hn) hRp hRc hRcomm hRexp hRG hσc hσd hσG hσG'

theorem threeNineThreeAlt_holds : ThreeNineThreeAlt := by
  intro X _ _ K E D X₁ d h hK
  rcases hK with hK | hK | hK | hK <;> obtain ⟨φ⟩ := hK
  · exact false_of_threeNineHyp_A6 h φ
  · exact false_of_threeNineHyp_alt_three h (Or.inl rfl) φ
  · exact false_of_threeNineHyp_alt_three h (Or.inr (Or.inl rfl)) φ
  · exact false_of_threeNineHyp_alt_three h (Or.inr (Or.inr rfl)) φ

end CFSG.LocalAnalysis.AGL81I.Section3
