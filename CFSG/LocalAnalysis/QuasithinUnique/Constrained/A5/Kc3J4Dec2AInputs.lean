
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Gen
public import CFSG.Sporadic.J4.QT2AData
public import CFSG.Sporadic.J4.QT2LocGenLem
public import CFSG.Sporadic.J4.QTOutLinGen

public section

namespace CFSG.QuasithinUnique.A5
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.A5.Dec2

@[expose] def a941q : List ℤ :=
  w5 (
    "aABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAbABAbaabAABAbaabAABAbaabAA" ++
    "BAbaabAABAbaabAABAbaabAABAbaabABbaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAA" ++
    "BAbaabAAABaCaBABBBBcBBCBcccBcACBCbAcaBABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaa" ++
    "bAABAbaabAbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaab" ++
    "AABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACbaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabA" ++
    "ABAbaabAABAbaabAABcaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAb" ++
    "aabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAb" ++
    "aabAABAbaabAABAbaabAABAbaabABBbaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABA" ++
    "baabAAABBcAcBaCaBaCaacCaBccABcaBaCBaeebABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abAABAbaabABbaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABcaABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABB" ++
    "acABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAABAbaabAAABaccbAbAcBAbaCBcBACaBCbCbaabcabACAcbCaabCCbbAAC" ++
    "BaabbcccAAbaaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAABacaBAABabaaB" ++
    "AABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaCAbbaBAABabaaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaaBAABabaaBAABabaBBcaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAC" ++
    "baaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaABaaaBAABabaaBAABabaaBAABa" ++
    "baaBAABabaaBAABabaaBAABabaaBAABabaAAcaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABab" ++
    "aaBAABabaCEEaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAbaABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABABcBAcBABcbbbcCaacBCCBACBACBeecABAba" ++
    "abAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACaaABAbaabAABAbaabAABAbaabAABAbaa" ++
    "bAABAbaabAABAbaabAABAbaabAAAbaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaa" ++
    "bAABcaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAACbbABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabABBacABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAABaaCCCB" ++
    "BAAbcaaBBccBAAcBCacaBACBAABcBcbAcabCbcABabCaBaBCCAbaaaBAABabaaBAABabaaBAABabaaBAABab" ++
    "aaBAABabaaBAABabaaBAABabaAABacaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABa" ++
    "baCAbbaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBBabaBAABabaaBAABabaaB" ++
    "AABabaaBAABabaaBAABabaaBAABabaaBAABabaBAcaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaaBAABabaACbaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaABbaBAABab" ++
    "aaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBEEAbcAbACbaCCbAcCAAcAbAcAbCaCbbaaa" ++
    "BAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAABbbaBAABabaaBAABabaaBAABaba" ++
    "aBAABabaaBAABabaaBAABabaaBAABabaBBabaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABaba" ++
    "aBAABabaBAcaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaACbaaBAABabaaBAA" ++
    "BabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaABcaBAABabaaBAABabaaBAABabaaBAABabaaBAAB" ++
    "abaaBAABabaaBAABabaCbaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBaBAABa" ++
    "baaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABababACaBcbcaCbCCCbcbbCbbbbabAcAbaaaBA" ++
    "ABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAABbaBAABabaaBAABabaaBAABabaaBA" ++
    "ABabaaBAABabaaBAABabaaBAABabaBaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAAB" ++
    "abaA")

@[expose] def a85q : List ℤ :=
  w5 (
    "ABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAbABAbaabAABAbaabAABAbaabAABA" ++
    "baabAABAbaabAABAbaabAABAbaabABcABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAba" ++
    "abACaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAcaABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabAABAbaabAABAbaabAABAbaabAACabABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAB" ++
    "AbaabAABAbaabABAbbABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabABBacABAbaa" ++
    "bAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabACAbaaABAbaabAABAbaabAABAbaabAABAba" ++
    "abAABAbaabAABAbaabAABAbaabAAABababABabcBaBBCBAABBCAACaCAbadeedEdededeedeedEdedEdEdee" ++
    "dEdEdaaABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAABAbaabAAAAAccABabcbcBaCCCBcB" ++
    "BccAACAABDeDeDEEDeDeDEDeDEEDEEDEDEDeDEEDABacAcaacbbaabcbbAbCBAbaBABAbaaaBAABabaaBAAB" ++
    "abaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaAABacaBAABabaaBAABabaaBAABabaaBAABabaaBAA" ++
    "BabaaBAABabaaBAABabaCAbbaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBBab" ++
    "aBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBAcaaBAABabaaBAABabaaBAABaba" ++
    "aBAABabaaBAABabaaBAABabaaBAABabaACaaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABaba" ++
    "aBAABabaAAcaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaCbaBAABabaaBAABab" ++
    "aaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaBaBAABabaaBAABabaaBAABabaaBAABabaaBAABabaaB" ++
    "AABabaaBAABaba")

end CFSG.QuasithinUnique.A5
