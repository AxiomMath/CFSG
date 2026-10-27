module

public import CFSG.Quasithin.H13.L32AC45a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC41c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk12
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk6

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem lemma14_7_45_a5_of_F4 (hN1 : LieSylowOver3) (hN2 : LieBorelInvert3) (h29 : Thm14_7_29_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h30 : Lemma14_7_30_F4)
    (h32 : Lemma14_7_32_F4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h42 : Lemma14_7_42_S5S3_F4)
    (h43 : Lemma14_7_43_F4) (h44 : Lemma14_7_44_F4) : Lemma14_7_45_A5_F4 := by
  intro G _ _ T L V H S K hK hHeq n hn hLie
  have hq := (h30 G T L V H S K hK).1
  have hKn := le_normalizer_of_setting hA37 hA38 S hK (h32 G T L V H S K hK)
  by_cases hl1K : l1 T L V ≤ K
  · rcases lemma14_7_41_two_F4 hN1 hN2 h29 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K with
      h | h | h
    · exact isAlt_five_of_isPSL hq.1 (odd_card_center_cStar K) h
    · exact absurd h (h43 G T L V H S K hK hHeq n hn hLie)
    · exact absurd h (h44 G T L V H S K hK hHeq n hn hLie)
  · obtain ⟨ρ, hρs, hρk⟩ := h42 G T L V H S K hK hHeq n hn hLie hl1K
    have := hq.2.1
    have : Nontrivial (cStar K) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center (cStar K))).nontrivial
    exact isAlt5_of_s5s3 hK hKn this hρs hρk

end CFSG.Quasithin.H13.L32A.C
