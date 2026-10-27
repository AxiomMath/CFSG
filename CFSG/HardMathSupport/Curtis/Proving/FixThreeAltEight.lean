module

public import Certificates.Certificate7154
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open Equiv

theorem card_of_two_group_le {J P : Subgroup (Perm (Fin 8))}
    (hJA : J ≤ alternatingGroup (Fin 8)) (hPJ : P ≤ J) (_hP2 : IsPGroup 2 P)
    (h64 : Nat.card P = 64) :
    Nat.card J = 64 ∨ Nat.card J = 192 ∨ Nat.card J = 576 ∨ Nat.card J = 1344 ∨
      Nat.card J = 20160 :=
  Certificates.certificate7154.2 J hJA (h64 ▸ Subgroup.card_dvd_of_le hPJ)

end CFSG.HardMathSupport.Curtis.Proving

end
