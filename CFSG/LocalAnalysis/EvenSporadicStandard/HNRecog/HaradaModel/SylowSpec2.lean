module

public import Certificates.Certificate441662

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

section Cert


theorem derived_eq : ⁅wordSubgroup sWords, wordSubgroup sWords⁆ = wordSubgroup tpWords :=
  Certificates.certificate441662.derived_eq

theorem w0_eq : wordSubgroup (tpWords ++ w0Extra) =
    closure ((wordSubgroup tpWords : Set (Equiv.Perm (Fin 1408))) ∪
      {y | y ∈ wordSubgroup sWords ⊓ blocks1408 ∧ y ^ 2 = 1}) :=
  Certificates.certificate441662.w0_eq

theorem card_T_a : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧
    g ^ 2 = elemA}.ncard = 80 :=
  Certificates.certificate441662.card_T_a

theorem card_T_az : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧
    g ^ 2 = elemA * elemZ}.ncard = 48 :=
  Certificates.certificate441662.card_T_az

theorem card_T'_a :
    {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemA}.ncard = 16 :=
  Certificates.certificate441662.card_T'_a

theorem card_T'_z :
    {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemZ}.ncard = 32 :=
  Certificates.certificate441662.card_T'_z

theorem card_T'_az :
    {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemA * elemZ}.ncard = 16 :=
  Certificates.certificate441662.card_T'_az

theorem card_W0_a : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup (tpWords ++ w0Extra) ∧
    g ^ 2 = elemA}.ncard = 48 :=
  Certificates.certificate441662.card_W0_a

theorem card_W0_az : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup (tpWords ++ w0Extra) ∧
    g ^ 2 = elemA * elemZ}.ncard = 16 :=
  Certificates.certificate441662.card_W0_az

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
