module

public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthLayerD

public section

namespace CFSG.ClassicalInvolution.WeakCT.SU4

open CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD

theorem su4SpinMinus_of_irr {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {b c : GaloisField p f} (hirr : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0) :
    SU4SpinMinus p f hirr := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  exact su4SpinMinus_exists hp2 hf hirr

theorem su4SpinMinus_galois {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    SU4SpinMinus p f (minusCoeffs_irr p f) :=
  su4SpinMinus_of_irr hp2 hq (minusCoeffs_irr p f)

end CFSG.ClassicalInvolution.WeakCT.SU4
