module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcWeylWords
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcTorusAct

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

noncomputable abbrev SM6 (l : List (Fin Tag.E6.rank)) : Matrix (Fin 6) (Fin 6) ℤ :=
  (l.map (Smat Tag.E6)).prod

abbrev RM6 (l : List (Fin Tag.E6.rank)) : Matrix (Fin 6) (Fin 6) ℤ :=
  (l.map (Rmat Tag.E6)).prod

theorem RM6_eq_SM6 (l : List (Fin Tag.E6.rank)) : RM6 l = SM6 l := by
  have : ∀ i : Fin Tag.E6.rank, Rmat Tag.E6 i = Smat Tag.E6 i := by decide +kernel
  have h : Rmat Tag.E6 = Smat Tag.E6 := funext this
  simp only [RM6, SM6, h]
  rfl

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
