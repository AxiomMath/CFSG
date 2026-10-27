module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAStarModel
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cert
public import Certificates.Certificate5251

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ComponentClassification.PSL3Four

theorem starModel_thm :
    StarModel := by
  obtain ⟨h₁, h₂, h₃, h₄, hc0⟩ := Certificates.certificate5251
  obtain ⟨z, hz⟩ := l34Facts
  refine ⟨?_, ?_, hc0⟩
  · intro p k hp x hxR hk
    have h1 := pow_eq_one_of_orderOf hz hp (x := (⟨x, hxR⟩ : ↥R)) (k := k)
      (by rw [Subgroup.orderOf_mk]; exact hk)
    simpa using congrArg Subtype.val h1
  · intro i p hp x hxR hxo hcomm
    fin_cases i
    · exact Or.inr (h₁ p hp x hxR hxo hcomm)
    · exact Or.inr (h₂ p hp x hxR hxo hcomm)
    · exact Or.inr (h₃ p hp x hxR hxo hcomm)
    · rcases h₄ p hp x hxR hxo hcomm with ⟨hp3, hxS⟩ | hc
      · exact Or.inl ⟨rfl, hp3, hxS⟩
      · exact Or.inr hc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
