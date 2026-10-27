module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem25Stmts
public import CFSG.GH74.QTGen4.Leaves.Ch12.ConfigGen4

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Open CFSG.Quasithin.H13

theorem lem12225N5_F4_holds : Lem12225N5_F4 := by
  intro G _ _ T L V H P U I h n p hH hNE hC
  exact Or.inl (n_eq_three_of_config_gen4 hC).1

theorem lem12225YNormal_F4_holds : Lem12225YNormal_F4 := by
  intro G _ _ T L V H P U I h n p hH hNE hC hn3
  exact absurd (n_eq_three_of_config_gen4 hC).1 hn3

theorem lem12225CTL3_F4_holds (hStar : Lem12225Star_F4) : Lem12225CTL3_F4 := by
  intro G _ _ T L V H P U I h n p hH hNE hC hn3
  obtain ⟨-, -, hR, hUL, -, -, -, hRe, -, -, -, -, -⟩ := hStar G T L V H P U I h n p hH hNE hC
  obtain ⟨-, hU16, -⟩ := n_eq_three_of_config_gen4 hC
  have hUR : U ≤ T ⊓ Subgroup.centralizer (U : Set G) := hR ▸ le_sup_left
  have hR16 := card_le_sixteen_of_isElemAbelian hRe
  have hURe : U = T ⊓ Subgroup.centralizer (U : Set G) :=
    Subgroup.eq_of_le_of_card_ge hUR (by omega)
  rw [eq_bot_iff, ← hUL]
  refine le_inf ?_ inf_le_right
  calc T ⊓ Subgroup.centralizer (L : Set G)
      ≤ U ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := le_sup_right
    _ = T ⊓ Subgroup.centralizer (U : Set G) := hR.symm
    _ = U := hURe.symm

end CFSG.GH74.QTGen4.Leaves
