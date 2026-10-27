module

public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.F2Words
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false

section E8Y

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}
  (S : LangSetup Tag.E8 L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 2)
  (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup Tag.E8} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L w)
  (hw2 : ∀ δ : Fin Tag.E8.rank → ℤ, w • w • δ = -δ)

include hw2

theorem iform_smul_self_eq_zero (δ : Fin Tag.E8.rank → ℤ) : iform (w • δ) δ = 0 := by
  have h1 : iform (w • δ) (w • w • δ) = iform δ (w • δ) := iform_smul w δ (w • δ)
  rw [hw2, iform_comm δ (w • δ)] at h1
  have h2 : iform (w • δ) (-δ) = -iform (w • δ) δ := by
    have := iform_smul_right (τ := Tag.E8) (-1) (w • δ) δ
    simpa using this
  rw [h2] at h1
  omega

theorem commute_rootSL2_smul_E8 {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (A B : SL2 L) :
    Commute (rootSL2 Tag.E8 L β A) (rootSL2 Tag.E8 L (w • β) B) :=
  CFSG.RankThree.PartOne.KE.e8_rootSL2_commute_of_orth hβ ((isRoot_smul_iff w).2 hβ)
    (by rw [dotProduct_mulVec_eq_iform, iform_comm]; exact iform_smul_self_eq_zero hw2 β) A B

end E8Y

end CFSG.HardMathSupport.Timmesfeld.CrossChar
