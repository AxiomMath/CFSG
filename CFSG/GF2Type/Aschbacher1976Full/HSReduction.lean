module

public import CFSG.GF2Type.Aschbacher1976Full.HSDefs
public import CFSG.Quasithin.Recognition.HSType17m

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint

theorem leafZ4Q8Sq_of_parts
    (hA : HSPartA) (hW : HSPartW) (hC : HSPartC) (hE : HSPartE) : Asc76LeafZ4Q8Sq := by
  intro G _ _ z hS hZ
  have hset : HSSetting G z := ⟨hS, hZ⟩
  have h1 : HSTI z := hA G z hset
  have h2 : HSWide z := hW G z hset h1
  have h3 : HSS5 z := hC G z hset h1 h2
  exact CFSG.Quasithin.HSType.statementI48_holds G (hE G z hset h1 h2 h3)

theorem hsPartW_of_cases (hCard : HSPartCard) (hBad : HSPartBad) (hTrans : HSPartTrans) :
    HSPartW := by
  intro G _ _ z hset hti
  obtain ⟨T, hTH, h⟩ := hCard G z hset hti
  have h8 : Nat.card (ET (T : Subgroup G) z) = 8 := by
    rcases h with h | h
    · exact (hBad G z hset hti ⟨T, hTH, h⟩).elim
    · exact h
  refine ⟨T, hTH, h8, ?_⟩
  by_contra hne
  exact hTrans G z hset hti ⟨T, hTH, h8, hne⟩

theorem leafZ4Q8Sq_of_cases
    (hA : HSPartA) (hCard : HSPartCard) (hBad : HSPartBad) (hTrans : HSPartTrans)
    (hC : HSPartC) (hE : HSPartE) : Asc76LeafZ4Q8Sq :=
  leafZ4Q8Sq_of_parts hA (hsPartW_of_cases hCard hBad hTrans) hC hE

end CFSG.GF2Type.Aschbacher1976Full.HS
