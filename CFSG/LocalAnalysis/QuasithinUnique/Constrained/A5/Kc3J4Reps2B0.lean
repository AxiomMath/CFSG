
module

public import CFSG.Sporadic.J4.QT2AMod
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2A

@[expose] def b1344Words : List (List ℤ) := [
  w5 (
    "EDeDEEDEEDEDEDeDEDEDEDEDEABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabA" ++
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaab" ++
    "AABAbaabAABAbaabAAAedededededEdededeedeedEde"),
  w5 (
    "cBAcBAEDeDEEDEEDEDEDeDEDEDEDEDEABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABaaABAbaabAABAbaabAABAbaabAABAbaabAA" ++
    "BAbaabAABAbaabAABAbaabAAAedededededEdededeedeedEdeabCabC"),
  w5 (
    "cBAcBAcBAcBAEDeDEEDEEDEDEDeDEDEDEDEDEABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abAbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABaaABAbaabAABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabAAAedededededEdededeedeedEdeabCabCabCabC"),
  w5 (
    "cBAcBAcBAcBAcBAcBAEDeDEEDEEDEDEDeDEDEDEDEDEABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaab" ++
    "AABAbaabAbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABaaABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAABAbaabAAAedededededEdededeedeedEdeabCabCabCabCabCabC")
]

@[expose] noncomputable def b1344Gens : List ↥J := b1344Words.map el5

@[expose] noncomputable def B1344 : Subgroup ↥J := Subgroup.closure {x | x ∈ b1344Gens}

@[expose] noncomputable def reps2B0 : List (Subgroup ↥J) := [B1344]

theorem B1344_mem_reps2B0 : B1344 ∈ reps2B0 := by simp [reps2B0]

end CFSG.QuasithinUnique.A5
