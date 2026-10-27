module

public import CFSG.ClassicalInvolution.RouteD.NoG2D4Multi
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Shared

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem multiStar_of_modelConnStar (hconn : ModelConnFactNe p) (hstar : ModelStarFact p) :
    MultiStar p f :=
  multiStar_of_sharedInvolution hconn hstar (G2D4.g2d4SharedInvolution p)

theorem multiPiece_of_modelConnStar (hconn : ModelConnFactNe p) (hstar : ModelStarFact p) :
    MultiPiece p f :=
  multiPiece_of_multiStar (multiStar_of_modelConnStar hconn hstar)

@[expose] def MultiModelFactsConnStar (p : ℕ) [Fact p.Prime] : Prop :=
  ModelConnFactNe p ∧ ModelStarFact p

theorem multiPiece_of_multiModelFactsConnStar (h : MultiModelFactsConnStar p) :
    MultiPiece p f :=
  multiPiece_of_modelConnStar h.1 h.2

end CFSG.ClassicalInvolution.RouteD
