module

public import CFSG.ClassicalInvolution.Phan.PhanQ19True
public import CFSG.ClassicalInvolution.Phan.PhanQ8Red
public import CFSG.ClassicalInvolution.Phan.PhanQ15Pent

public section

namespace CFSG.ClassicalInvolution.PhanQ

open CFSG.ClassicalInvolution.PhanP CFSG.ClassicalInvolution.PhanG
  CFSG.ClassicalInvolution.PhanD4

section Final

set_option linter.unusedSectionVars false

variable (p f : ℕ) [Fact p.Prime]

theorem phanD4ShortCycleTrue_of_cone_quadNull
    (hcone : ∀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f),
      ConeFact (stdModel hp2 hq).S ((stdModel hp2 hq).ptStep0 hp2 hq))
    (hquad : ∀ (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f), QuadNull (ptGraph (stdModel hp2 hq).S)) :
    PhanD4ShortCycleTrue p f := fun hp2 hq =>
  ⟨hcone hp2 hq, hquad hp2 hq,
    apexPentagon_of_pairPent _ hp2 hq fun a c d hcd => pairPent_std _ hp2 hq a c d hcd⟩

end Final

end CFSG.ClassicalInvolution.PhanQ
