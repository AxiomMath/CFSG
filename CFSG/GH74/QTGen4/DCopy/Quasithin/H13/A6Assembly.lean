module

public import CFSG.Quasithin.H13.A6Assembly
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {G : Type} [Group G]

open scoped IsMulCommutative in

theorem stmt13_4_1_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1335 : Stmt13_3_5_F4) (h1349 : Stmt13_4_9_F4)
    (h13410 : Stmt13_4_10_17_F4) : Stmt13_4_1_F4 := by
  intro G _ _ T L V hH hV hZV
  obtain ⟨-, -, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hc, hmod⟩ := hall V hV
  have hA6V : IsA6On L V := by
    rcases hmod with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, hc6⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact absurd h hZV
    · exact absurd h hZV
    · exact nonempty_mulEquiv_of_realizes (altCoreModel_faithful (by norm_num)) hc6
    · exact absurd h hZV
    · exact absurd h hZV
  obtain ⟨z, hz, hzL, hzM⟩ := (h1335 G T L V hH hV).2.2 hA6V
  exact h1349 G T L V z hH hV hZV hz hzL hzM (h13410 G T L V z hH hV hZV hz hzL hzM)

open scoped IsMulCommutative in

theorem stmt13_5_2_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h13316 : Stmt13_3_16_F4) (h1341 : Stmt13_4_1_F4) :
    Stmt13_5_2_F4 := by
  intro G _ _ T L hH hSp K hK
  obtain ⟨hfive, ⟨hTK, hmaxK, -, -⟩, ⟨hex, hall⟩, h4⟩ := h1332 G T L hH K hK
  have hU33 : ¬ LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSU 3 3 1 := by
    intro hu
    have hnA5 : ¬ quasithinO2QuotientIso K (alternatingGroup (Fin 5)) := fun hA5 =>
      not_alt5_of_psu33 hu ((quasithinO2QuotientIso_iff K _).1 hA5)
    exact h13316 G T K (h4 (Or.inl hnA5)) hu
  refine ⟨?_, ⟨hTK, hmaxK⟩, hex, fun VK hVK => ?_⟩
  · rcases hfive with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd h hU33
  · obtain ⟨hVT, hTV, hfsu, hc, hmod⟩ := hall VK hVK
    refine ⟨hVK.1, hVT, hTV, hfsu, ?_⟩
    rcases hmod with ⟨h5, h5c⟩ | ⟨h6, h6c⟩ | ⟨-, hcard2, hcore⟩ | ⟨-, hsl, hslc⟩ | ⟨hu, -, -⟩
    · exact ⟨h5c, hc, Or.inl h5⟩
    · exact ⟨h6c, hc, Or.inr (Or.inl h6)⟩
    · exfalso
      have hne : VK ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard2
        exact absurd hcard2 (by norm_num)
      by_cases hA5 : quasithinO2QuotientIso K (alternatingGroup (Fin 5))
      · have hKN : K ≤ Subgroup.normalizer (VK : Set G) := hVK.2.2.1
        obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altCoreModel_faithful (by norm_num)) hcore
        obtain ⟨φ, hφ⟩ := exists_surjective_autOn hKN
        exact false_of_surjective_alt6_of_alt5 hA5 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
      · exact hSp (h1341 G T K VK (h4 (Or.inl hA5)) hVK hne)
    · exact ⟨hslc, hc, Or.inr (Or.inr hsl)⟩
    · exact absurd hu hU33

end CFSG.Quasithin.H13.A6
