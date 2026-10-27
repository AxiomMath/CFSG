module

public import CFSG.ClassicalInvolution.Phan.PhanS2Struct
public import CFSG.ClassicalInvolution.Phan.PhanH9Final

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.ClassicalInvolution.PhanB3.H CFSG.LieType.Universal CFSG.LieType.Universal.Spin

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PhanB3StdPointGeometry (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → p ^ f % 4 = 3 →
    ∀ (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2) (h2 : (2 : GaloisField p f) ≠ 0)
      (C : B2Coord hK (GaloisField p f) h2) (M : ModelB3 p f h2)
      (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))),
      GoodFamily E → (∀ i, (E.ι i).range = M.U i) → PhanB3PointGeometry E

theorem phanB3Std_of_pointGeometry (hg : PhanB3StdPointGeometry p f) :
    PhanB3StdSimplyTwoConnected p f :=
  fun hp2 hq hmod hK h2 C M E hgood hrange =>
    (hg hp2 hq hmod hK h2 C M E hgood hrange).simplyTwoConnected_phanSystem

end CFSG.ClassicalInvolution.PhanB3.S
