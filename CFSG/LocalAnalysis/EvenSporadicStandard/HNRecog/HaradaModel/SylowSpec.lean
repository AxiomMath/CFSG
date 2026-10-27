module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.BasicCheck
import Certificates.Kernel.HN1408.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Coe
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import Certificates.Certificate441662
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

section Cert

theorem sylow_card : Nat.card ↥(wordSubgroup sWords) = 2 ^ 11 :=
  Certificates.certificate441662.sylow_card

theorem elemA_mem_sylow : elemA ∈ wordSubgroup sWords :=
  Certificates.certificate441662.a_mem

theorem elemZ_mem_sylow : elemZ ∈ wordSubgroup sWords :=
  Certificates.certificate441662.z_mem

theorem elemZ_comm_T {g : Equiv.Perm (Fin 1408)} (hg : g ∈ wordSubgroup sWords)
    (hE : g ∈ blocks1408) : elemZ * g = g * elemZ :=
  Certificates.certificate441662.z_comm_T g hg hE

theorem centre_T {g : Equiv.Perm (Fin 1408)} (hg : g ∈ wordSubgroup sWords) (hE : g ∈ blocks1408)
    (hc : ∀ y ∈ wordSubgroup sWords, y ∈ blocks1408 → g * y = y * g) :
    g = 1 ∨ g = elemA ∨ g = elemZ ∨ g = elemA * elemZ :=
  Certificates.certificate441662.centre_T g hg hE hc

theorem centralizer_T_le (hP : Nat.card ↥P1408 = 177408000) {x : Equiv.Perm (Fin 1408)}
    (hx : x ∈ P1408) (hc : ∀ y ∈ wordSubgroup sWords, y ∈ blocks1408 → x * y = y * x) :
    x ∈ blocks1408 :=
  Certificates.certificate441662.centralizer_T_le hP x hx hc

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
