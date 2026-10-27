module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Phan.PhanB5Block
public import CFSG.ClassicalInvolution.Phan.PhanS7Ctx
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3 CFSG.ClassicalInvolution.Phan

section Close

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]

@[expose] def PlaneClose (E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f))))
    (D : KDat (GaloisField p f) (GaloisField p (2 * f))) : Prop :=
  ∀ g ∈ (E.ι 0).range ⊔ (E.ι 1).range, LineFix g (vXi D) → g ∈ parab E {1}

end Close

section PiDet

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

@[expose] def PiDetOne (g : spinGroup (quadOdd 3 F)) : Prop :=
  ∃ M : Matrix (Fin 3) (Fin 3) K, M.det = 1 ∧
    actK g (vXi D) = M 0 0 • vXi D + M 1 0 • vE2 D + M 2 0 • vE3 D ∧
    actK g (vE2 D) = M 0 1 • vXi D + M 1 1 • vE2 D + M 2 1 • vE3 D ∧
    actK g (vE3 D) = M 0 2 • vXi D + M 1 2 • vE2 D + M 2 2 • vE3 D

end PiDet

end CFSG.ClassicalInvolution.PhanB3.S
