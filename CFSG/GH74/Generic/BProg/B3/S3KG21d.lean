module

public import CFSG.GH74.Generic.BProg.B3.S3KG21dFour
public import CFSG.GH74.Generic.BProg.B3.S3KG21dThree
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1

public section

namespace CFSG.GH74.Generic.BProg.B3

open S3KG

theorem kg21d_proved : Kg21d := by
  intro F _ _ hodd V hV h4
  have : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := by
    intro h2
    have h := FiniteField.even_card_iff_char_two.mp h2
    rw [← Nat.card_eq_fintype_card] at h
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases lt_or_ge 3 (Nat.card F) with h3 | h3
  · exact exists_inner_of_three_lt hF h3 V hV h4
  · have h2 : 1 < Nat.card F := Finite.one_lt_card
    have h3' : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact exists_inner_of_card_eq_three h3' V h4

end CFSG.GH74.Generic.BProg.B3
