module

public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Closing
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.RankThree.PartOne.KE.A1SL2

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcHighThree


structure E8FiveFrameElt (K : Type) [Field K] [Finite K] where
  ω : (AlgebraicClosure K)ˣ
  hω : orderOf ω = 5
  z : adjointGroup Tag.E8 K
  Dz : ModGL Tag.E8 (AlgebraicClosure K)
  Q : ModGL Tag.E8 (AlgebraicClosure K)
  s : ℕ
  hDz : Dz ∈ adjointGroup Tag.E8 (AlgebraicClosure K)
  hQ : Q ∈ adjointGroup Tag.E8 (AlgebraicClosure K)
  hs : ¬ 5 ∣ s
  hFDz : ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
    Units.map (entrywiseHom Fr) Dz = Dz * Q
  hQd : Q * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) ω) * Q⁻¹ =
    rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) ω) ^ s
  hz : baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL Tag.E8 K) =
    Dz * rootDiagUnit Tag.E8 (Pi.mulSingle (4 : Fin Tag.E8.rank) ω) * Dz⁻¹
  frame : ∃ X : Subgroup (adjointGroup Tag.E8 K), ClosingFrameAt z X

end CFSG.LieType.SeitzGeneration.ExcHigh
