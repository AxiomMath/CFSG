
module

public import CFSG.Monster.Existence.TwoPoint.Fi22Check
public import CFSG.Monster.Existence.TwoPoint.HNCheck
public import CFSG.Monster.Existence.TwoPoint.HNTwoBCheck
public import CFSG.Monster.Existence.TwoPoint.ThCheck
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs
public import CFSG.Monster.Existence.TwoPoint.ThreeVCheck
public import CFSG.Monster.Existence.TwoPoint.ThreeVOriginalFalseInputs
public import CFSG.Monster.Existence.TwoPoint.Y433MCheck

public section

namespace CFSG.KC.KDenseP.TwoPoint

open CFSG.Monster.AxisCount CFSG.Monster.Existence
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)
open CFSG.Sporadic.Bridge.SurjD.Native (hnRels)

abbrev Pairs := List (List Native.Gen × List Native.Gen)

@[expose] def tp3 (eqs nes : Pairs) : Pairs := eqs ++ eqs ++ eqs ++ nes

@[expose] def tauP (l : Pairs) : Pairs := l.map fun e => (e.1 ++ [.tau], e.2 ++ [.tau])

@[expose] def fiRels (idx : List Nat) : Pairs := idx.map fun i => (fiRelW rels[i]!, [])

@[expose] def hnR (idx : List Nat) : Pairs := idx.map fun i => (hnRelW hnRels[i]!, [])

@[expose] def thR (idx : List Nat) : Pairs :=
  idx.map fun i => (thRelW TauCeti.Sporadic.Thompson.presentation.relatorLetters[i]!, [])

@[expose] def yW (j : Nat) : List Native.Gen := fiCAlpha ++ gxProdWord (gxXList j)

@[expose] def bpW : List Native.Gen := fiWAlpha ++ fiWBeta ++ fiWAlpha

@[expose] def gxNode (j : Nat) : Pairs :=
  (if j = 9 then [] else [(yW j ++ fiWAlpha, yW j)]) ++ [(yW j ++ bpW, yW j)]

@[expose] def p6046 : Pairs :=
  tp3 [(fiRhoT ++ fiCGamma, fiCGamma ++ fiWU[0]!), (fiRhoT ++ fiCDelta, fiCDelta ++ fiWDelta)] []
@[expose] def p6047 : Pairs :=
  tp3 [(fiRhoT ++ fiCAlpha, fiCAlpha ++ fiWAlpha), (fiWAB ++ fiCThreeA, fiCThreeA ++ wordThreeA)] []
@[expose] def p6048 : Pairs :=
  tp3 ((List.range 10).map (fun i => (fiWAlpha ++ fiWU[i]!, fiWU[i]! ++ fiWAlpha)) ++
      (List.range 10).map (fun i => (fiWBeta ++ fiWU[i]!, fiWU[i]! ++ fiWBeta)) ++
      [(fiWAlpha ++ fiWAlpha, []), (fiWBeta ++ fiWBeta, []), (fiWAB ++ fiWAB ++ fiWAB, [])])
    (tauP [(fiWAB, []), (fiWU[3]!, [])])
@[expose] def p6049 : Pairs := tp3 (fiRels [0, 7, 9, 17, 21, 26, 41, 47, 48, 52]) []
@[expose] def p6050 : Pairs := tp3 (fiRels [4, 11, 14, 22, 29, 35, 38, 45, 53]) []
@[expose] def p6051 : Pairs := tp3 (fiRels [5, 13, 24, 27, 31, 37, 39, 40, 49]) []
@[expose] def p6052 : Pairs := tp3 (fiRels [1, 3, 16, 20, 28, 32, 46, 51]) []
@[expose] def p6053 : Pairs := tp3 (fiRels [10, 12, 15, 25, 33, 34, 36, 42, 50, 54]) []
@[expose] def p6054 : Pairs := tp3 (fiRels [2, 6, 8, 18, 19, 23, 30, 43, 44]) []
@[expose] def p6055 : Pairs := fiRels [55]
@[expose] def p6056 : Pairs := fiRels [55]
@[expose] def p6057 : Pairs := fiRels [55]
@[expose] def p6058 : Pairs := tp3 (fiRels [56]) []
@[expose] def p6059 : Pairs :=
  tp3 ([0, 1, 2, 3, 4, 5, 6, 7, 9].map (fun i => (s4WGamma ++ fiWU[i]!, fiWU[i]! ++ s4WGamma))) []
@[expose] def p6060 : Pairs :=
  tp3 [(fiRhoT ++ s4CGamma, s4CGamma ++ s4WGamma),
    (fiRhoT ++ s4CBetaGamma, s4CBetaGamma ++ s4WBetaGamma)] []
@[expose] def p6061 : Pairs :=
  tp3 [(s4WGamma ++ s4WGamma, []), (fiWU[8]! ++ fiWU[8]!, []), (s4WGamma ++ fiWBeta, fiWBeta ++ s4WGamma),
      (s4WE8Gamma ++ s4WE8Gamma ++ s4WE8Gamma, []),
      (s4WAlphaGamma ++ s4WAlphaGamma ++ s4WAlphaGamma, [])]
    [(s4WE8Gamma, []), (s4WAlphaGamma, [])]
@[expose] def p6063 : Pairs := [2, 3, 4, 5].flatMap gxNode
@[expose] def p6064 : Pairs := [6, 7, 8].flatMap gxNode
@[expose] def p6065 : Pairs := [9, 10].flatMap gxNode
@[expose] def p6066 : Pairs := [11, 12].flatMap gxNode
@[expose] def p6067 : Pairs := [13, 14].flatMap gxNode
@[expose] def p6068 : Pairs := [15, 16].flatMap gxNode
@[expose] def p6069 : Pairs := [17, 18].flatMap gxNode
@[expose] def p6070 : Pairs := [19, 20].flatMap gxNode
@[expose] def p6071 : Pairs :=
  tauP [(yW 21 ++ fiWAlpha, yW 21)] ++ [(yW 21 ++ bpW, yW 21)] ++ gxNode 22
@[expose] def p6072 : Pairs := tp3 [(gxXWord ++ gxCW9, gxCW9 ++ gxProdWord (gxXList 9))] []
@[expose] def p6073 : Pairs :=
  tp3 [(hnRhoT ++ hnCAlpha, hnCAlpha ++ hnWAlpha), (hnRhoT ++ hnCBeta, hnCBeta ++ hnWBeta), (hnWAB5, [])] []
@[expose] def p6074 : Pairs :=
  tp3 ((List.range 5).map (fun i => (hnWU[i]! ++ hnWV[i]!, [])) ++
      (List.range 5).map (fun i => (hnWAlpha ++ hnWU[i]!, hnWU[i]! ++ hnWAlpha)) ++
      (List.range 5).map (fun i => (hnWBeta ++ hnWU[i]!, hnWU[i]! ++ hnWBeta)))
    [(hnWAB, []), (hnWU[4]!, [])]
@[expose] def p6075 : Pairs := tp3 (hnR [4, 5, 6, 7, 10, 11, 12]) []
@[expose] def p6076 : Pairs := tp3 (hnR [0, 1, 2, 3, 8, 9]) []
@[expose] def p6077 : Pairs := tp3 (hnR [13, 14, 15]) []
@[expose] def p6078 : Pairs := tp3 (hnR [16, 17, 18]) []
@[expose] def p6079 : Pairs := tp3 [(hnXWord ++ hnCW, hnCW ++ hnWW)] []
@[expose] def p6080 : Pairs :=
  tp3 ((List.range 8).map (fun i => (thWAlpha ++ thWU[i]!, thWU[i]! ++ thWAlpha))) []
@[expose] def p6081 : Pairs :=
  tp3 ((List.range 8).map (fun i => (thWBeta ++ thWU[i]!, thWU[i]! ++ thWBeta))) []
@[expose] def p6082 : Pairs :=
  tp3 [(thRhoT ++ thCAlpha, thCAlpha ++ thWAlpha), (thRhoT ++ thCBeta, thCBeta ++ thWBeta),
    (wordThreeC ++ thWG, thWG ++ thWAB)] []
@[expose] def p6083 : Pairs :=
  tp3 ((List.range 8).map (fun i => (thWU[i]! ++ thWV[i]!, [])) ++ [(thWAB3, []), (thWS7, [])])
    (tauP [(thWAB, []), (thWU[5]!, [])])
@[expose] def p6084 : Pairs := tp3 (thR [13]) []
@[expose] def p6085 : Pairs := tp3 (thR [0, 2, 33, 35]) []
@[expose] def p6086 : Pairs := tp3 (thR [7, 14, 38]) []
@[expose] def p6087 : Pairs := tp3 (thR [5, 32, 37]) []
@[expose] def p6088 : Pairs := tp3 (thR [3, 8, 9, 16, 19, 22]) []
@[expose] def p6089 : Pairs := tp3 (thR [1, 10, 12, 18, 24, 25, 26, 28, 30, 31, 34, 36]) []
@[expose] def p6090 : Pairs := tp3 (thR [4, 6, 11, 15, 17, 20, 21, 23, 27, 29]) []
@[expose] def p6091 : Pairs :=
  tp3 [(wordThreeA ++ wordKA, wordKA ++ wordMonoA), (wordMonoA ++ wordMonoA ++ wordMonoA, []),
    (wordThreeC ++ wordKC, wordKC ++ wordMonoC), (wordMonoC ++ wordMonoC ++ wordMonoC, [])] []
@[expose] def p6092 : Pairs := tp3 [(fiRhoT ++ fiCAlphaGamma, fiCAlphaGamma ++ fiWAlphaGamma)] []
@[expose] def p6093 : Pairs :=
  tp3 [(fiRhoT ++ fiCT2, fiCT2 ++ fiWT2), (gxXWord ++ fiCT2Alpha, fiCT2Alpha ++ (fiWT2 ++ fiWAlpha))] []
@[expose] def p6094 : Pairs := tp3 [(y433RelW y433F213R, [])] []
@[expose] def p6095 : Pairs := tp3 [(y433RelW y433F312R, fiWBeta)] []
@[expose] def p6096 : Pairs := tp3 [(y433RelW y433SpiderR, [])] []

end CFSG.KC.KDenseP.TwoPoint

end
