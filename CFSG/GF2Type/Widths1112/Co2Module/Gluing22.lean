module

public import Certificates.Certificate38960
public import Certificates.Certificate38961

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open CFSG.GF2W1112 CFSG.Sporadic.SmallF2 Matrix

@[expose] def uM0 : Matrix (Fin 22) (Fin 22) (ZMod 2) := rowsMatrix 22 w12UM0Rows

theorem hEnum_co2
    (θ : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2)) (M : Matrix (Fin 22) (Fin 22) (ZMod 2))
    (hY : ∀ k : Fin 3, M * Xfin 1 (uSigma (iY k)) (cfTab uW1 uV0 (uU (iY k))) =
      Xfin 1 (uSigma (iZ k)) (cfTab uW1 uV0 (uU (iZ k))) * M)
    (h3 : M ^ 3 = 1)
    (hrel : ∀ j, (wordProd (fun s => Xfin (θ s) (uSigma (iN s)) (cfTab uW1 uV0 (uU (iN s))))
      (uTw j) * M) ^ uKk j = 1) :
    ∃ S : Matrix (Fin 2) (Fin 2) (ZMod 2), IsUnit S ∧
      (∀ s, Qfin S * Xfin (θ s) (uSigma (iN s)) (cfTab uW1 uV0 (uU (iN s))) = uX0 s * Qfin S) ∧
      Qfin S * M = uM0 * Qfin S := by
  obtain ⟨c, rfl⟩ := Certificates.certificate38960 M hY
  exact Certificates.certificate38961 c θ h3 hrel

end CFSG.GF2Type.Widths1112.Co2Module
