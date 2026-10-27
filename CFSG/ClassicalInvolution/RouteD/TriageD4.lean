module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenMain

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem rowExoticD4 : RowPiece p f ShapeExoticD4 :=
  rowExoticD4_of_four exoticD4Four

end CFSG.ClassicalInvolution.RouteD.Exotic
