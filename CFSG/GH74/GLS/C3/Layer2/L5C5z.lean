module

public import CFSG.GH74.GLS.C3.Layer2.L5C5
public import CFSG.GH74.GLS.C3.Layer2.L5C5f
public import CFSG.GH74.GLS.C3.Layer2.L5C18

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

theorem sh2_contract
    : Sh2Contract (ι := Fin 4) Sh2 inc where
  rec2 := fun _ _ _ κ hκ hidx hmove => rec2 κ hκ hidx hmove
  e16 := sh2_E16
  move := sh2_move
  engine := fun ty _ h => engine2 ty h

end CFSG.GH74.GLS.C3.Layer2.L5
