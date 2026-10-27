module

public import CFSG.ClassicalInvolution.Phan.PhanQ20Final

public section

namespace CFSG.ClassicalInvolution.PhanQ

open CFSG.ClassicalInvolution.PhanP CFSG.ClassicalInvolution.PhanG
  CFSG.ClassicalInvolution.PhanD4

section Wire

set_option linter.unusedSectionVars false

variable (p f : ℕ) [Fact p.Prime]

structure PhanD4ConeQuad : Prop where
  cone : ∀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f),
    ConeFact (stdModel hp2 hq).S ((stdModel hp2 hq).ptStep0 hp2 hq)
  quad : ∀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f), QuadNull (ptGraph (stdModel hp2 hq).S)

variable {p f}

theorem PhanD4ConeQuad.shortCycleTrue (H : PhanD4ConeQuad p f) : PhanD4ShortCycleTrue p f :=
  phanD4ShortCycleTrue_of_cone_quadNull p f H.cone H.quad

theorem phanD4Geometry_of_coneQuad (H : PhanD4ConeQuad p f) : PhanD4Geometry p f :=
  phanD4Geometry_of_shortCycleTrue H.shortCycleTrue

end Wire

end CFSG.ClassicalInvolution.PhanQ
