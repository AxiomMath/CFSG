module

public import CFSG.ClassicalInvolution.Phan.PhanQ26Wire
public import CFSG.ClassicalInvolution.Phan.PhanQ35QuadNull

public section

namespace CFSG.ClassicalInvolution.PhanQ

open CFSG.ClassicalInvolution.PhanP CFSG.ClassicalInvolution.PhanG
  CFSG.ClassicalInvolution.PhanD4

section Wire2

set_option linter.unusedSectionVars false

variable (p f : ℕ) [Fact p.Prime]


@[expose] def PhanD4Cone : Prop :=
  ∀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f),
    ConeFact (stdModel hp2 hq).S ((stdModel hp2 hq).ptStep0 hp2 hq)

variable {p f}

theorem PhanD4Cone.coneQuad (H : PhanD4Cone p f) : PhanD4ConeQuad p f :=
  ⟨H, fun hp2 hq => quadNull_std _ hp2 hq⟩

theorem phanD4Geometry_of_cone (H : PhanD4Cone p f) : PhanD4Geometry p f :=
  phanD4Geometry_of_coneQuad H.coneQuad

end Wire2

end CFSG.ClassicalInvolution.PhanQ
