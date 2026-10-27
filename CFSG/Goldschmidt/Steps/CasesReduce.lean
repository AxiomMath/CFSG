module

public import CFSG.Goldschmidt.StatementsG
import CFSG.Goldschmidt.Steps.PropHSetup
public import CFSG.Goldschmidt.StatementsH

public section

namespace CFSG.Goldschmidt

theorem propH_compType_of_cases (h7 : S_G7) (h8 : S_G8) : S_propH_compType := by
  intro G _ _ _ hnab hIH hcomp hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin
  obtain ⟨-, hU4, -, -, -, -⟩ := N31 G hnab S A U hAS hAab hAcl hUA hUmin
  by_cases h8U : 8 ≤ Nat.card U
  · exact h7 G hnab hIH hcomp hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin h8U
  · have hUp : IsPGroup 2 U := (S.isPGroup').to_le hUmin.1
    obtain ⟨e, he⟩ := hUp.exists_card_eq
    have he2 : e = 2 := by
      rw [he] at hU4 h8U
      rcases Nat.lt_or_ge e 3 with h | h
      · by_contra hne
        have h1 : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · exact absurd (Nat.pow_le_pow_right (show 0 < 2 by norm_num) h) (by omega)
    exact h8 G hnab hIH hcomp hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin
      (by rw [he, he2]; norm_num)

end CFSG.Goldschmidt
