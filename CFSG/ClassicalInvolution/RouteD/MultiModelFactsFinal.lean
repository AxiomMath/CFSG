module

public import CFSG.ClassicalInvolution.RouteD.MultiModelFacts
public import CFSG.ClassicalInvolution.RouteD.MultiModelShortU5
public import CFSG.ClassicalInvolution.RouteD.MultiModelShortE6
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Final

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime]

theorem modelConnExotic : ModelConnExotic p := by
  intro t n e _ hadm hp2 _ hx
  rcases hx with ⟨rfl, rfl⟩ | rfl
  · exact commFamilyConnected_psu_five hp2 hadm
  · obtain rfl : n = 0 := hadm.2.2
    exact commFamilyConnected_twistedE6 hp2 hadm

theorem modelConnFactNe : ModelConnFactNe p :=
  modelConnFactNe_of_exotic modelConnExotic

theorem multiModelFactsConnStar : MultiModelFactsConnStar p :=
  ⟨modelConnFactNe, modelStarFact⟩

theorem multiPiece_proved {f : ℕ} : MultiPiece p f :=
  multiPiece_of_multiModelFactsConnStar multiModelFactsConnStar

end CFSG.ClassicalInvolution.RouteD
