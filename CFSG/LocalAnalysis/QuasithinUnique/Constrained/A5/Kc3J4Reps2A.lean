module

public import CFSG.Sporadic.J4.QT2AMod

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def a21Masks : List ℕ := [1056, 321, 43, 796]

@[expose] def a77Masks : List ℕ := [768, 299, 213, 1414]

@[expose] noncomputable def A21 : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ a21Masks.map (eta uJ 11)}

@[expose] noncomputable def A77 : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ a77Masks.map (eta uJ 11)}

@[expose] def a941Words : List (List ℤ) := [
  w5 (
    "cABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACaaABAbaabAABAbaabAABAbaabA" ++
    "ABAbaabAABAbaabAABAbaabAABAbaabAAAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabA" ++
    "ABAbaabABBacABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABCbCCBACbaBCaCaACCbABaabcccaC"),
  w5 (
    "aABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAcABAbaabAABAbaabAABAbaabAA" ++
    "BAbaabAABAbaabAABAbaabAABAbaabACbaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABcaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACbaaABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABAAAAbbccBCBcAbBAbCaaacBABAAc"),
  w5 (
    "aABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAbABAbaabAABAbaabAABAbaabAA" ++
    "BAbaabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABA" ++
    "baabACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabA" ++
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabA" ++
    "ABAbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBbaaABA" ++
    "baabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABaccAbccbACbabaAAbACbbAccabAc"),
  w5 (
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAacABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAA" ++
    "BAbaabAAABcABBAbcACABBcABaBaCAbbaCCBaa")
]

@[expose] noncomputable def a941Gens : List ↥J := a941Words.map el5

@[expose] noncomputable def A941 : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ a941Gens}

@[expose] def a85Words : List (List ℤ) := [
  w5 (
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabAABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBacABAbaa" ++
    "bAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAAABababABabcBaBBCBAABBCAACaCAbadeedEdededeedeedEdedEdEdee" ++
    "dEdEdaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAaaABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabAABAbaabAAAbACABcbcBCCAbabAcacBcAbcaCAcDeDeDEEDeDeDEDeDE" ++
    "EDEEDEDEDeDEEDABacAcaacbbaabcbbAbCBAbaBABAbaaaBAABabaaBAABabaaBAABabaaBAABabaaBAABab" ++
    "aaBAABabaaBAABabaAABacaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaCAbbaB" ++
    "AABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBBabaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaaBAABabaaBAABabaaBAABabaBAcaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaACaaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAAcaBAABabaaBAABab" ++
    "aaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaCbaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaa" ++
    "BAABabaaBAABabaBaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABaba"),
  w5 (
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabAABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBacABAbaa" ++
    "bAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAAABababABabcBaBBCBAABBCAACaCAbadeedEdededeedeedEdedEdEdee" ++
    "dEdEdbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABaaABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABA" ++
    "baabAABAbaabAACbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBaBCAcAcaa" ++
    "acBCbCCCCAbcAABaaCBDeDeDEEDeDeDEDeDEEDEEDEDEDeDEEDABacAcaacbbaabcbbAbCBAbaBABAbaaaBA" ++
    "ABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAABacaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaaBAABabaaBAABabaaBAABabaCAbbaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaBBabaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBAcaaBAABabaaBAABa" ++
    "baaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaACaaaBAABabaaBAABabaaBAABabaaBAABabaaBAABa" ++
    "baaBAABabaaBAABabaAAcaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaCbaBAAB" ++
    "abaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBaBAABabaaBAABabaaBAABabaaBAABaba" ++
    "aBAABabaaBAABabaaBAABaba"),
  w5 (
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabAABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBacABAbaa" ++
    "bAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAAABababABabcBaBBCBAABBCAACaCAbadeedEdededeedeedEdedEdEdee" ++
    "dEdEdaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAbABAbaabAABAbaabAABAb" ++
    "aabAABAbaabAABAbaabAABAbaabAABAbaabABbaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABbaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABABabbABab" ++
    "baBCaBabCbAcbaBcabCDeDeDEEDeDeDEDeDEEDEEDEDEDeDEEDABacAcaacbbaabcbbAbCBAbaBABAbaaaBA" ++
    "ABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAABacaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaaBAABabaaBAABabaaBAABabaCAbbaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaBBabaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBAcaaBAABabaaBAABa" ++
    "baaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaACaaaBAABabaaBAABabaaBAABabaaBAABabaaBAABa" ++
    "baaBAABabaaBAABabaAAcaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaCbaBAAB" ++
    "abaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBaBAABabaaBAABabaaBAABabaaBAABaba" ++
    "aBAABabaaBAABabaaBAABaba"),
  w5 (
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabAABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBacABAbaa" ++
    "bAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAAABababABabcBaBBCBAABBCAACaCAbadeedEdededeedeedEdedEdEdee" ++
    "dEdEdABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabAABAbaabAABAbaa" ++
    "bAABAbaabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabA" ++
    "ABAbaabACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABAbbABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBbACABcbcBCCAbabAcacBcAbcaCAcDeDeDEEDeDe" ++
    "DEDeDEEDEEDEDEDeDEEDABacAcaacbbaabcbbAbCBAbaBABAbaaaBAABabaaBAABabaaBAABabaaBAABabaa" ++
    "BAABabaaBAABabaaBAABabaAABacaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABaba" ++
    "CAbbaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBBabaBAABabaaBAABabaaBAA" ++
    "BabaaBAABabaaBAABabaaBAABabaaBAABabaBAcaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAA" ++
    "BabaaBAABabaACaaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAAcaBAABabaa" ++
    "BAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaCbaBAABabaaBAABabaaBAABabaaBAABabaaBA" ++
    "ABabaaBAABabaaBAABabaBaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABaba")
]

@[expose] noncomputable def a85Gens : List ↥J := a85Words.map el5

@[expose] noncomputable def A85 : Subgroup ↥J :=
  Subgroup.closure {x | x ∈ a85Gens}

@[expose] noncomputable def reps2A : List (Subgroup ↥J) := [A21, A77, A941, A85]

theorem A21_mem_reps2A : A21 ∈ reps2A := by simp [reps2A]

theorem A77_mem_reps2A : A77 ∈ reps2A := by simp [reps2A]

theorem A941_mem_reps2A : A941 ∈ reps2A := by simp [reps2A]

theorem A85_mem_reps2A : A85 ∈ reps2A := by simp [reps2A]

end CFSG.QuasithinUnique.A5
