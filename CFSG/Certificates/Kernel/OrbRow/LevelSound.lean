module

public import CFSG.Certificates.Kernel.OrbRow.WordRep

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum CFSG.KS

theorem getS_eq : ∀ (S : List ℕ) (j : ℕ), getS S j = S.getD j 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: S, j + 1 => getS_eq S j

theorem getLs_eq : ∀ (L : List (List ℕ)) (j : ℕ), getLs L j = L.getD j []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, j + 1 => getLs_eq L j

theorem lenS_eq : ∀ L : List ℕ, lenS L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenS_eq L)

theorem levelK_eq (n w m : ℕ) (S : List ℕ) (k : ℕ) (B K M D : List ℕ) (R : List (List ℕ))
    (i : ℕ) : levelK n w m S k B K M D R i =
      rowsK n w m S k (getS M i) (getS D i) (getS B i) (getS K i) (getLs R i) := by
  unfold levelK
  rw [strictB_apply, strictB_apply, strictB_apply, strictB_apply]

end CFSG.KC.OrbRow

end
