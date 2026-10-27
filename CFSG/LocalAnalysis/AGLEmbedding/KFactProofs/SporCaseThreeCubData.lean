module

public import Certificates.Data.CFSGNative.CTP.StrongP
public meta import Certificates.Data.CFSGNative.CTP.StrongP

public section

namespace CFSG.AGLEmbedding.SporCubic

open CFSG.SectionRank.Native

@[expose] def mclSylow5HData : CubData :=
  { mclSylow5Data with rh := 0, oh := 3, a := 1, b := 3, c := 4, d := 3, k := 3, l := 0, μ := 1 }

@[expose] def co2Sylow5HData : CubData :=
  { co2Sylow5Data with rh := 0, oh := 3, a := 4, b := 1, c := 4, d := 0, k := 0, l := 0, μ := 1 }

@[expose] def co3Sylow5HData : CubData :=
  { co3Sylow5Data with
    nregs := 19
    prog := co3Sylow5Data.prog ++ [
      .pow 2 0 16, .pow 3 1 17, .pow 0 0 18, .mul 18 16 18, .mul 18 17 18, .mul 18 16 18,
      .mul 18 17 18, .mul 18 17 18, .mul 18 0 18, .mul 18 1 18, .mul 18 16 18, .mul 18 1 18,
      .mul 18 1 18, .mul 18 0 18, .mul 18 1 18, .mul 18 1 18, .mul 18 16 18, .mul 18 17 18,
      .mul 18 0 18]
    rh := 18
    oh := 8
    a := 3
    b := 1
    c := 4
    d := 2
    k := 2
    l := 3
    μ := 2 }

@[expose] def thSylow5HData : CubData :=
  { thSylow5Data with
    nregs := 15
    prog := thSylow5Data.prog ++ [.pow 3 0 14]
    rh := 14
    oh := 2
    a := 4
    b := 0
    c := 0
    d := 4
    k := 0
    l := 0
    μ := 1 }

@[expose] def onSylow7HData : CubData :=
  { onSylow7Data with
    nregs := 15
    prog := onSylow7Data.prog ++ [
      .pow 3 1 13, .pow 0 0 14, .mul 14 13 14, .mul 14 13 14,
      .mul 14 0 14, .mul 14 13 14, .mul 14 0 14, .mul 14 13 14,
      .mul 14 13 14, .mul 14 0 14, .mul 14 13 14, .mul 14 13 14,
      .mul 14 0 14, .mul 14 13 14, .mul 14 0 14, .mul 14 13 14,
      .mul 14 0 14, .mul 14 1 14, .mul 14 1 14, .mul 14 0 14,
      .mul 14 13 14, .mul 14 0 14, .mul 14 13 14, .mul 14 0 14,
      .mul 14 13 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14,
      .mul 14 13 14, .mul 14 0 14, .mul 14 13 14, .mul 14 13 14,
      .mul 14 0 14, .mul 14 1 14, .mul 14 0 14, .mul 14 13 14,
      .mul 14 13 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14,
      .mul 14 13 14, .mul 14 0 14, .mul 14 1 14, .mul 14 0 14]
    rh := 14
    oh := 6
    a := 3
    b := 0
    c := 0
    d := 3
    k := 0
    l := 5
    μ := 2 }

end CFSG.AGLEmbedding.SporCubic
