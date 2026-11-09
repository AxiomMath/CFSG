module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem wordK_append (n w m idn : Nat) (S SI : Nat → Nat) (a b : List Int) :
    wordK n w m idn S SI (a ++ b) = wordK n w m (wordK n w m idn S SI b) S SI a := by
  induction a with
  | nil => rfl
  | cons z a ih =>
    rw [List.cons_append]
    unfold wordK at ih ⊢
    dsimp only
    rw [ih]

end CFSG.KS.Raw

end
