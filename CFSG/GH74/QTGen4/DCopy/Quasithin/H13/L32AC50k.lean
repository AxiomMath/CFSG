module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32AC50k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC50c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC50g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC50j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

theorem lemma14_7_50_of_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h2 : Lemma14_7_2_F4) (h4 : Lemma14_7_4_two_three_F4)
    (h28 : Lemma14_7_28_F4) (h29 : Thm14_7_29_F4) (h32 : Lemma14_7_32_F4) (h47 : Lemma14_7_47_F4)
    (h48 : Lemma14_7_48_F4) (hMod : Lemma14_7_50_Mod_F4) : Lemma14_7_50_F4 := by
  intro G _ _ T L V H S K hK hA
  obtain ⟨π, hker, hA7⟩ := exists_pi_a7_F4 h37 h38 h28 h32 h47 h48 S hK hA
  obtain ⟨π', hker', hA7', hT⟩ := exists_pi_a7_ts S π hker hA7
  obtain ⟨K', hcK', hHKT, -⟩ := h48 _ T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hL1K := (h47 _ T L V H S K hK).1
  obtain ⟨I, hV1I, hIU, hIn, hcase⟩ := hMod G T L V H S K hK hHKT hL1K hA π' hker' hA7'
  rcases hcase with ⟨hr, Δ, hΔ, hst⟩ | ⟨β, -, hβker, hβ⟩
  · have hPT : (T.subgroupOf H).map π' = Alt7.taSub := by
      rcases hT with ⟨htop, -⟩ | ⟨-, hPT⟩
      · exfalso
        have h1 := Alt7.card_alt7
        rw [← hr, htop, Subgroup.card_top, Alt7.card_perm7] at h1
        omega
      · exact hPT
    exact false_of_four_F4 h1222 h1332 h1334 h29 S hker' hr hPT hIn hΔ hst
  · exact false_of_six_F4 h1222 h1332 h1334 h2 h4 S hker' hT hV1I hIU hIn hβker hβ

end CFSG.Quasithin.H13.L32A.C
