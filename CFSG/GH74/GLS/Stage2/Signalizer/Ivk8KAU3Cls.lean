module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kay_U3_of_classes (hI5 : KAU3I5) (hI3 : KAU3I3) (hII5 : KAU3II5) (hII3 : KAU3II3) :
    KAY FU3 := by
  refine kay_of_kaAll ?_
  intro Y _ _ hY _ α hα2 hα1
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hLie
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ p ^ f := by
    have h2 := hp.two_le
    have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨m, hm⟩ := hodd
    omega
  have hq : p ^ f = 3 ∨ 5 ≤ p ^ f := by
    obtain ⟨m, hm⟩ := hodd
    omega
  by_cases hin : α ∈ innSub Y
  · rcases hq with hq | hq
    · exact hI3 p f F hp hp2 hf hq hF Y ⟨e⟩ α hin hα2 hα1
    · exact hI5 p f F hp hp2 hf hq hF Y ⟨e⟩ α hin hα2 hα1
  · rcases hq with hq | hq
    · exact hII3 p f F hp hp2 hf hq hF Y ⟨e⟩ α hin hα2
    · exact hII5 p f F hp hp2 hf hq hF Y ⟨e⟩ α hin hα2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
