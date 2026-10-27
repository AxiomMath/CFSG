module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem oTwoUpper_le_centralizer_zS152_F4 {T Mc M P : Subgroup G} (hs : Setting152 T Mc M)
    (h15209 : StageNotation15209_F4) (h15211 : StageLemma15211_F4) (h15213 : StageLemma15213_F4)
    {B₀ : Subgroup (MulAut (V154 T Mc M))} (hB₀ : IsB0 T Mc M B₀) (hP : IsHStar T M P) :
    oTwoUpper P ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
  obtain ⟨B, hB⟩ := (h15209 G T Mc M hs P hP).sigmaPrime_nonempty
  obtain ⟨B₀', hB₀', huniq, hprop⟩ := (h15213 G T Mc M hs P hP).exists_B0
  have hB₀eq : B₀ = B₀' := huniq B₀ hB₀
  subst hB₀eq
  obtain ⟨-, -, hZ, -⟩ := hprop B hB
  have := (h15211 G T Mc M hs P hP B hB).centralizes
  rw [hZ] at this
  exact this

end CFSG.Quasithin
