module

public import CFSG.ClassicalInvolution.Asc77.AscC25X7
public import CFSG.ClassicalInvolution.Asc77.AscC25X8
public import CFSG.ClassicalInvolution.Asc77.AscC25X11

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace C25X

section Final

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G}


variable (p) in
theorem nc4Fact_proved : NC4Fact p :=
  nc4Fact_of_rows (nc4SL p) (nc4SU p) (nc4Spin7 p) (nc4D4P p) (nc4D4M p)

theorem layer_a_typed_proved {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨ LayerOrthType p f Ω a 5 true ∨
      LayerOrthType p f Ω a 6 (!piSign p f) :=
  layer_a_typed (nc4Fact_proved p) hyp ha2 ha1 haR haR'

end Final

end C25X

end CFSG.ClassicalInvolution.Asc77
