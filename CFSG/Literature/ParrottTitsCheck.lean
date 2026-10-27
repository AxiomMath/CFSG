module

public import Certificates.Certificate2004

public section

namespace CFSG.Literature.ParrottTits

open CFSG.CosetTable CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2

theorem card_PG_le :
    Finite (PG 10 parrottWords) ∧ Nat.card (PG 10 parrottWords) ≤ 17971200 :=
  Certificates.certificate2004.1

theorem parrott_perms : ∃ x : ℕ → Equiv.Perm (Fin 1755),
    (∀ w ∈ parrottWords, FreeGroup.lift (fun i : Fin 10 => x i) (FreeGroup.mk w) = 1) ∧
    ∀ j < 2, permOfArr 1755 titsDerivedArrs[j]! =
      wordIn 10 x ([parrottD0Word, parrottD1Word].getD j []) :=
  Certificates.certificate2004.2

end CFSG.Literature.ParrottTits
