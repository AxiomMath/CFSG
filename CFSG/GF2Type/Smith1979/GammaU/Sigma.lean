module

public import Certificates.Certificate16981

public import CFSG.GF2Type.Smith1979.GammaU.SigmaBase
import all CFSG.GF2Type.Smith1979.GammaU.SigmaBase

public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairBase

public section

namespace CFSG.GF2Type.Smith1979.GammaU.SigmaP

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.GammaU.ResPair Module
open scoped commutatorElement

variable {i : ℕ}

section

variable (hi : i = 0 ∨ i = 1)
include hi

theorem facts : SigmaFacts i := Certificates.certificate16981 i hi

theorem orbit_subset : ∀ U ∈ n2 i, ∃ y ∈ s45 i, U (vecOf a0) = vecOf y := (facts hi).orbit_subset

theorem orbit_reach : ∀ x ∈ s45 i, ∃ U ∈ n2 i, U (vecOf a0) = vecOf x := (facts hi).orbit_reach

theorem finrank_sigma : finrank (ZMod 2) (sigma i) = 6 := (facts hi).finrank_sigma

theorem orbit_mem_sigma : ∀ x ∈ s45 i, vecOf x ∈ sigma i := (facts hi).orbit_mem_sigma

theorem sigma_le_span :
    sigma i ≤ Submodule.span (ZMod 2) {v | ∃ x ∈ s45 i, vecOf x = v} :=
  (facts hi).sigma_le_span

theorem card_p2 : Nat.card (p2 i) = 17280 := (facts hi).card_p2

theorem commutator_n2 : ⁅n2 i, n2 i⁆ = p2 i := (facts hi).commutator_n2

theorem theta0_mem_p2 : ∃ U ∈ p2 i, ∀ v, U v = theta0 v := (facts hi).theta0_mem_p2

end

end CFSG.GF2Type.Smith1979.GammaU.SigmaP
