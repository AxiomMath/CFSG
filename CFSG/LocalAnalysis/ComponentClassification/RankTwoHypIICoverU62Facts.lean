module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Words
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.LargeExtraspecial.SMod20AutPlane

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U62

open Subgroup CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Fischer (T46 t46G)
open CFSG.Sporadic.Schreier (evalCodes)

@[expose] noncomputable def u62Let :
    List (Equiv.Perm (Fin 693)) :=
  (List.finRange 46).map fun k : Fin 46 => t46G ((k.val : ℤ) + 1)

@[expose] noncomputable def u62SbG :
    List (Equiv.Perm (Fin 693)) :=
  u62SbWords.map (evalCodes u62Let)

@[expose] noncomputable def u62Sb :
    Subgroup (Equiv.Perm (Fin 693)) :=
  closure {g | g ∈ u62SbG}

@[expose] noncomputable def u62Phi : Equiv.Perm (Fin 693) :=
  CFSG.LargeExtraspecial.SMod20.Aut.fieldPerm CFSG.LargeExtraspecial.SMod20.Aut.frob4

@[expose] noncomputable def u62R (j : ℕ) : Equiv.Perm (Fin 693) :=
  evalCodes u62SbG (u62RWords.getD j [])

@[expose] def U62Facts : Prop :=
  (∀ q : Fin 693, (∀ g ∈ u62SbG, g q = q) ↔ q = 0) ∧
    Nat.card u62Sb = 32768 ∧ u62Phi ∉ u62Sb ∧
    (∀ g ∈ u62SbG, u62Phi * g * u62Phi⁻¹ ∈ u62Sb) ∧
    (∀ u ∈ u62Sb, orderOf u = 2 → ∃ j < 43, ∃ c ∈ u62Sb, u = c * u62R j * c⁻¹) ∧
    ∀ j < 43, ∀ s ∈ u62Sb, (s * u62Phi) ^ 2 = 1 → s * u62Phi * u62R j = u62R j * (s * u62Phi) →
      MonoW T46 false (closure {u62R j, s * u62Phi})

end CFSG.ComponentClassification.RankTwoHypIICover.U62

end
