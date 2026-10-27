module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleE6
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleE8
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleF4
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleTwistedE6

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem rowSingleExc : RowPiece p f ShapeSingleExc :=
  rowSingleExc_of_parts rowSingleF4 rowSingleE6 rowSingleE8 rowSingleTwistedE6

end CFSG.ClassicalInvolution.RouteD.Exotic
