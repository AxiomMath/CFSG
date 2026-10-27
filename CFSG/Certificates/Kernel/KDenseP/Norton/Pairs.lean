module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.FiveTorusInputs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenDatum
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.ThreeBInputs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data

public section

namespace CFSG.KC.KDenseP.Norton

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.MON11_13 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.Gen11 CFSG.AGLEmbedding.Norton.Gen13

abbrev Prs := List (List Native.Gen × List Native.Gen)

@[expose] def tri (eqs nes : Prs) : Prs := eqs ++ eqs ++ eqs ++ nes

@[expose] def tauS (w : List Native.Gen) : List Native.Gen × List Native.Gen :=
  (w ++ [.xi, .tau], [.xi, .tau])

@[expose] def e125201 : Prs := qCommPairs ++ wInvPairs
@[expose] def e125202 : Prs := wQSelfPairs ++ wQOtherPairs
@[expose] def n125206 : Prs := [(qW 0, []), (qW 1, []), (qW 2, [])]
@[expose] def e125211 : Prs := sevenCommPairs ++ sevenActPairs
@[expose] def n125212 : Prs := [tauS dW, (zW, [])] ++ (List.range 7).map fun k => (sevenNeWord k, [])
@[expose] def e125221 : Prs := sevenYPairs ++ sevenIPairs
@[expose] def n125223 : Prs :=
  (List.range 7).map (fun k => tauS (sevenNeXWord k)) ++ (List.range 7).map fun k => (sevenNeYWord k, [])
@[expose] def e125360 : Prs := tbOrderPairs ++ tbWOrderPairs
@[expose] def n125360 : Prs := [tauS tbW]
@[expose] def e125500 : Prs := [(powL 13 thirteenX, [])]
@[expose] def e125501 : Prs :=
  [(thirteenX ++ thirteenXi, []), (thirteenK ++ thirteenKi, []),
    (thirteenYi ++ thirteenXi ++ thirteenY ++ thirteenX, thirteenZ),
    (thirteenX ++ thirteenZ, thirteenZ ++ thirteenX), (thirteenK ++ thirteenZ, thirteenZ ++ thirteenK),
    (thirteenT0 ++ thirteenX ++ thirteenT0, thirteenXi), (thirteenT0 ++ thirteenK, thirteenK ++ thirteenT0),
    (thirteenT0 ++ thirteenT0, [])]
@[expose] def n125501 : Prs := [(thirteenZ, [])]
@[expose] def e125502 : Prs :=
  [(powL 11 gen11W0, []), (powL 11 gen11W1, []), (gen11W0 ++ gen11W1, gen11W1 ++ gen11W0),
    (gen11W0 ++ gen11W2, gen11W2 ++ powL 6 gen11W0 ++ powL 3 gen11W1),
    (gen11W0 ++ gen11W3, gen11W3 ++ powL 4 gen11W1), (gen11W0 ++ gen11W4, gen11W4 ++ powL 3 gen11W0),
    (gen11W0 ++ thirteenT0, thirteenT0 ++ gen11W0)]
@[expose] def n125502 : Prs := [tauS gen11W0]
@[expose] def e125552 : Prs := [(powL 13 genD13W0, []), (powL 13 genD13W2, []), (powL 13 genD13W1, [])]
@[expose] def e125553 : Prs :=
  [(genD13W0 ++ genD13W1, genD13W1 ++ genD13W0), (genD13W2 ++ genD13W1, genD13W1 ++ genD13W2),
    (genD13W0 ++ genD13W2, powL 4 genD13W1 ++ genD13W2 ++ genD13W0), (genD13W8, powL 3 genD13W4)]
@[expose] def n125553 : Prs := [tauS genD13W1]
@[expose] def e125554 : Prs :=
  [(genD13W0 ++ genD13W3, genD13W3 ++ powL 6 genD13W0 ++ powL 10 genD13W2 ++ powL 11 genD13W1)]
@[expose] def e125555 : Prs :=
  [(genD13W2 ++ genD13W3, genD13W3 ++ powL 1 genD13W0 ++ powL 7 genD13W2 ++ powL 3 genD13W1)]
@[expose] def e125556 : Prs :=
  [(genD13W0 ++ genD13W4, genD13W4 ++ powL 7 genD13W0 ++ powL 7 genD13W2 ++ powL 8 genD13W1)]
@[expose] def e125557 : Prs :=
  [(genD13W2 ++ genD13W4, genD13W4 ++ powL 5 genD13W0 ++ powL 7 genD13W2 ++ powL 6 genD13W1)]
@[expose] def e125558 : Prs :=
  [(genD13W1 ++ genD13W5, genD13W5 ++ powL 12 genD13W1),
    (genD13W2 ++ genD13W5, genD13W5 ++ powL 12 genD13W1 ++ powL 12 genD13W2)]
@[expose] def e125559 : Prs :=
  [(genD13W1 ++ genD13W6, genD13W6 ++ powL 12 genD13W2), (genD13W2 ++ genD13W6, genD13W6 ++ powL 1 genD13W1)]
@[expose] def e125560 : Prs :=
  [(gen13W0 ++ thirteenX, thirteenX ++ gen13W0), (gen13W1 ++ thirteenX, thirteenX ++ gen13W1),
    (thirteenK ++ thirteenZ, thirteenZ ++ thirteenK), (gen13W5 ++ thirteenZ, thirteenZ ++ gen13W5),
    (gen13W6 ++ thirteenZ, thirteenZ ++ gen13W6), (gen13W7 ++ thirteenZ, thirteenZ ++ gen13W7),
    (thirteenT0 ++ thirteenZ, thirteenZ ++ thirteenT0)]
@[expose] def e125561 : Prs :=
  [(genD13W1 ++ genD13W7, genD13W7 ++ powL 12 genD13W1),
    (genD13W2 ++ genD13W7, genD13W7 ++ powL 10 genD13W1 ++ powL 8 genD13W2)]

end CFSG.KC.KDenseP.Norton

end
