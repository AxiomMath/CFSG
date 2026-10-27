module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23PinNative

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

set_option compiler.extract_closed false

@[expose] def y13Str : String :=
    "BaAAaabbaaBBaBbAaaBbBabBbAbbbaabaBBaBBabAaABBBAaaBaAAaabBAAabABAbABBaAAaabbaaBBaBbAaaBbBab" ++
    "BbAbbbaabaBBaBBabAaABBBAaaBaAAaabBAAabABAbAB"

@[expose] def g13Str : String :=
    "BaBaBBBAAAaBbAbaBBaAbAabbABabaBBAAaaBBAbABbaBababaabbabBAbbabbBabBbAbaBaAbBaaaabBAbABbAbba" ++
    "aBbAbaBabbBaaBbaabBaBBbAbbaAAbABaBbabbaBBbAABBAABbaBaBabBaAABAaaAAAAABBBABAaAabaBABBbaABbb" ++
    "BABbabbABBBBaABaabAAabbAABBabBabbabAaBABbbaAabbAabBAAAAAabBBaBbABbbbAbaAABbAbbbbAbbaBABbaa" ++
    "aAaBabABbAbaABBABaAaaABAbAaaaaAbbbBaABbabABbABBBbabBabbbBabbAAaaABaaBbaAaAbBBBBBBbbAaaBbBA" ++
    "baabBAAABABaBBBBaAabaBAbBBAbBbbaBbBbaBaaaaabaABbAAAbbaBaabaaaaBBAbbaAAABBaBAabAAABaAABabba" ++
    "ABBbaabbaAabBabAAbABBAbaBAabbBAaabaAabaBaabaBAbbaABAbAbAbAbABABABABAbABABABAbABAbbAbabbbBb" ++
    "BBbBBAaBbBAaaaBABABAabBBBBBABABBabaBbabAABaaaBBbbbbaAbABBAaBAAbbBaAbaBAAAbaaBAaaaBAAbBbABa" ++
    "AaaAAbBbBBABAaaBAaabABaAAaAbAbbaaaAbbAababbABBbBaBaBabABbaaBaaaBbAbaAaAbaBBaaabBAAaAAAbAab" ++
    "aaBabBbbBBBAbbBABbABbBaBbabABBBBbabAaBaaAABaabAAAaaAbBAABaBbBabAbbbbABBAAAaAaABaaBbaAbaBAB" ++
    "bbaaBaBABAaBaBbaAaBBbAaBBBBAaBAbBbAABBbBAABAABBBBABaBbbaaAaaabbbbaBBaBBBBbBABAbBaBaBbaBAAB" ++
    "BBabBABAabAABaABBbAaBabBAbBBaaABAbAbbBAaABABaAABAbABaaaaabbBbBBABbABbAbBbBBBaAAaaaaBABaBba" ++
    "BabbbbAAaAAaabbBbAaBbaAAAabBbaAaBBaaAaaAABAbAbAbAbABAbAbABAbAbABBabaBababaBabababaBaBabaBa" ++
    "BaBbbbabaAaAabbbaaBbbABBBbbBAAABabaAabbAaAAaABAbBABaaaaBabbabABAbBBBABABAbaBbbbBBBABabBABa" ++
    "AbBBAabaBbBBAABAaaBaAbBbaAAbBBbABAaBBAabbabaAbbbAABbaAbbbbBbABBaAaABAabAbBBAAAAbaAaAABBaaa" ++
    "aBbbABAAababbBbBBBAabaBABbBBabaBAAAAbbbBBbbabaAbBBbabbbABAAAbAbAAbAabaaabbAAAaBBBBbBBBaBBb" ++
    "aabaAABbaBBBBBbbaaAABBaBbaAbAaabBaaAaBabBbaaBbaAAabbBAbABbAbbAAAaAbAabbAbABAAaBaBabAabaBbA" ++
    "bAbabBBABbAaabBBabBABBaAbbbbABabBAabBBAaBBAbAaAAbBAaBabBBaAABBaBbbAbBBBBbabbbabbabAaBBABaA" ++
    "bbbaaAaABBBBAABbaaaABBaAAAbbBBbbbbBAabAABabbAbBAbbaaBBaBaBabaBaBabababaBaBabababaaAAaAAabb" ++
    "AAABABBbbbAABabbBABAaaBABaAaAaBbabABbBAAAAbBAABbBBBAaAbBBAAaAbAabbBBbBAbabbbAAAaBabAbbbbAB" ++
    "aABBAabaABaaBbBBbABaBbAaBAabAaBABABAaBAAaaBABaaAbABAbBAABababAaBAaAbbAbAABAaAAAbBabaBaABAA" ++
    "BbaAAAAabAbaBAbbBBBaAbAbbBbbabAbbaaabaBbaABaBbBbbAbAaBaBAbAAbBABBABABAaaaBBAAaabbAAAbBaBaB" ++
    "BAbaBbAAbaaaaBBbbabBBbBaAbbBBaAbAAABBBAAabbbBaAAaabAabbbBbBaBaaAABAbaAABaabBbbbbBbbbBAabBA" ++
    "bBBBAAbBAAaBaaBbABbAbaaaabbbBaBbaaaBaABBBAbabBABBbABBAAbbBBBbbAbaabbBBBbbAaabbAabAbAAbbBAB" ++
    "bBAbbaaAbABBAbaBbAbAbbbAaBAbBAABBAbAAaAab"

@[expose] def strLetters (s : String) : List Int :=
  s.toList.map fun c => if c = 'a' then 1 else if c = 'A' then -1 else if c = 'b' then 2 else -2

@[expose] def y13Letters : List Int := strLetters y13Str

@[expose] def g13Letters : List Int := strLetters g13Str

@[expose] def fi23Pin13OK (O : WOrbit) : Bool :=
  let TY := wordT 31671 (genTables O) y13Letters
  let TG := wordT 31671 (genTables O) g13Letters
  let TD := dTable O
  eqTab (powT 31671 13 TY) (idT 31671) && !eqTab TY (idT 31671) &&
    eqTab (compT 31671 TY TG) (compT 31671 TG (powT 31671 4 TY)) &&
    eqTab (compT 31671 TD TY) (compT 31671 TY TD) && eqTab (powT 31671 2 TD) (idT 31671) &&
    !eqTab TD (idT 31671)

end CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23PinNative
