module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Main
import CFSG.Goldschmidt.Steps.CasesReduce
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt

theorem G7_of (h4 : S_G4) (h72 : S_G72) (h76 : S_G76) : S_G7 := by
  intro G _ _ _ hnab hIH _ hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin h8
  have hset := h4 G hnab hIH hrank hnoSE S A U hAS hAab hAcl hUA hUmin
  have hE := h72 G hnab hIH hrank hnoSE S A U hAS hAab hAcl hUA hUmin h8
  exact hSnab ((h76 G S U hset h8 hE).2.1 S)

theorem G8_of (h4 : S_G4) (h89 : S_G89) : S_G8 := by
  intro G _ _ _ hnab hIH _ hrank hnoSE S hSnab A U hAS hAab hAcl hUA hUmin h4U
  exact h89 G S U (h4 G hnab hIH hrank hnoSE S A U hAS hAab hAcl hUA hUmin) h4U hSnab

theorem coreStatement_of_paper
    (h4 : S_G4) (h72 : S_G72) (h76 : S_G76) (h89 : S_G89) :
    CoreStatement :=
  coreStatement_of_propH_compType (propH_compType_of_cases (G7_of h4 h72 h76) (G8_of h4 h89))

end CFSG.Goldschmidt
