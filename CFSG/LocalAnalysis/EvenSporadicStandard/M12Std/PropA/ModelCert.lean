module

public import Certificates.Certificate450010

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup

theorem model_of_certificate (b : Bool) :
    Model (K28 b) D28 pT x28 ∧ Nat.card ↥(K28 b) = 380160 ∧
      ∀ y ∈ D28, orderOf y = 2 → Nat.card ↥(D28 ⊓ centralizer ({y} : Set (Perm (Fin 28)))) = 240 →
        ∃ a ∈ D28, a * y * a⁻¹ = x28 :=
  Certificates.certificate450010 b

end CFSG.EvenSporadicStandard.M12Std.PropA
