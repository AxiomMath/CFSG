module

public import Certificates.Data.ONanG28T

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree

open CFSG.AGLEmbedding.KFactProofs.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def commCode (A B : Array ℕ) : Bool := mulCode A B == mulCode B A

@[expose] def g28CenterTXCheck : Bool :=
  (List.range 243).all fun n =>
    !(commCode txL[n]! tU && commCode txL[n]! tZ && commCode txL[n]! tO) ||
      txL[n]! == idCode || txL[n]! == tzc || txL[n]! == mulCode tzc tzc

end CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree
