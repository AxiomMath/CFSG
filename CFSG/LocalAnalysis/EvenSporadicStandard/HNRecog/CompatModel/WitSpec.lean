module

public import Certificates.Certificate441872

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog

section Cert


theorem witSylow_spec :
    Nat.card ↥(closure (elemW '' {w | w ∈ witSylow})) = 256 ∧
      closure (elemW '' {w | w ∈ witSylow}) ≤
        P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) ∧
      ∀ s ∈ closure (elemW '' {w | w ∈ witSylow}), orderOf s = 2 →
        s = elemA ∨ s = elemB ∨ s = elemA * elemB ∨
          ∃ w : ↥P1408, ModelVertex w ∧ (w : Equiv.Perm (Fin 1408)) * s = s * w :=
  Certificates.certificate441872

end Cert

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
