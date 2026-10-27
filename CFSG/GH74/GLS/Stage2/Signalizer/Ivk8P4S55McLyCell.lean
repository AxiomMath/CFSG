module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55LyObs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55McLN1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem n1fam_mcly :
    N1Fam FMcLy := by
  intro Y _ _ p b R₀ hF hcfg
  obtain ⟨hpp, hp2, hord, hsyl, hpg⟩ := hcfg
  have : Fact p.Prime := ⟨hpp⟩
  rcases hF with hMcL | hLy
  · exact (McLN1.mcl_n1_false hMcL hp2 hord hsyl hpg).elim
  · obtain ⟨hp3, E, hE5, hEb, z, hzE, hzne⟩ := LyObs.ly_hhobs hLy hp2 hord hsyl hpg
    refine Or.inr ⟨5, ⟨Nat.prime_five, ?_, E, hE5, fun h => absurd h (by norm_num), hEb, z, hzE,
      hzne⟩, fun h => absurd h (by norm_num)⟩
    omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
