module

public import CFSG.ClassicalInvolution.Phan.PhanS23SigmaE

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

theorem qF_nondegenerate : qF.Nondegenerate := by
  have : Invertible (2 : ZMod 7) := invertibleOfNonzero (by decide)
  unfold qF
  exact QuadraticMap.nondegenerate_weightedSumSquares (R := ZMod 7)
    (w := (![1, 1, 1, 1, 1, 1, -1] : Fin 7 → ZMod 7))
    (fun i => by
      rw [isRegular_iff_ne_zero]
      fin_cases i <;> decide)

theorem familyWitt7_of_witt
    (hW : ∀ {F : Type} [Field F] [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] {Q : QuadraticForm F V}, Q.Nondegenerate →
      ∀ {ι : Type} [Fintype ι] (v w : ι → V),
        (∀ i j, QuadraticMap.polar Q (v i) (v j) = QuadraticMap.polar Q (w i) (w j)) →
        (∀ c : ι → F, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0) →
        ∃ e : Q.IsometryEquiv Q, ∀ i, e (v i) = w i) : FamilyWitt7 := by
  intro ι _ v w h1 h2
  have : Invertible (2 : ZMod 7) := invertibleOfNonzero (by decide)
  exact hW qF_nondegenerate v w h1 h2

theorem sigmaWitt_of_witt
    (hW : ∀ {F : Type} [Field F] [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] {Q : QuadraticForm F V}, Q.Nondegenerate →
      ∀ {ι : Type} [Fintype ι] (v w : ι → V),
        (∀ i j, QuadraticMap.polar Q (v i) (v j) = QuadraticMap.polar Q (w i) (w j)) →
        (∀ c : ι → F, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0) →
        ∃ e : Q.IsometryEquiv Q, ∀ i, e (v i) = w i) : SigmaWitt :=
  sigmaWitt_of_familyWitt7 (familyWitt7_of_witt hW)

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
