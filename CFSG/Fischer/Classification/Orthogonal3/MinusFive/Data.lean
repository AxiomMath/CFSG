module

public import CFSG.Fischer.Classification.PartIII.Beta.Data

public section

namespace CFSG.Fischer.Classification.MinusFive

open CFSG.Fischer.Classification.Beta

@[expose] def qM (x : Fin 6 → ZMod 2) : ZMod 2 :=
  x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 + x 4 * x 4 + x 5 * x 5 +
    x 0 * x 2 + x 2 * x 3 + x 3 * x 4 + x 4 * x 5 + x 1 * x 3

@[expose] def polM (x y : Fin 6 → ZMod 2) : ZMod 2 := qM (x + y) - qM x - qM y

@[expose] def tM (a b : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := b + polM b a • a

@[expose] def rQ (w v : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 := v + dot5 2 v w • w

@[expose] def mPt : Fin 36 → Fin 6 → ZMod 2 :=
  ![![1, 0, 0, 1, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 0, 0, 1],
    ![1, 1, 1, 0, 0, 1], ![1, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 1], ![1, 0, 1, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 1, 1, 0], ![1, 1, 0, 0, 1, 0], ![1, 1, 0, 0, 1, 1], ![0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 0], ![0, 1, 1, 1, 1, 0], ![1, 1, 1, 0, 1, 1],
    ![1, 1, 1, 1, 1, 0], ![0, 1, 1, 0, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 0],
    ![0, 1, 1, 0, 1, 0], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 1]]

@[expose] def mTab : List (Fin 36) :=
  [0, 1, 8, 0, 12, 14, 0, 0, 6, 0, 9, 0, 13, 11, 2, 5, 25, 0, 0, 17, 0, 0, 32, 34,
    31, 0, 16, 0, 20, 22, 26, 28, 15, 0, 0, 7, 0, 0, 3, 4, 0, 0, 0, 10, 0, 0, 0, 0,
    30, 0, 0, 18, 0, 0, 29, 27, 24, 0, 19, 0, 23, 21, 35, 33]

@[expose] def encM (x : Fin 6 → ZMod 2) : ℕ :=
  (x 0).val + 2 * ((x 1).val + 2 * ((x 2).val + 2 * ((x 3).val + 2 * ((x 4).val +
    2 * (x 5).val))))

@[expose] def mIdx (x : Fin 6 → ZMod 2) : Fin 36 := mTab.getD (encM x) 0

theorem qM_mPt : ∀ i : Fin 36, qM (mPt i) = 1 := by
  decide +kernel

theorem mPt_mIdx : ∀ a b c d e f : ZMod 2, qM ![a, b, c, d, e, f] = 1 →
    mPt (mIdx ![a, b, c, d, e, f]) = ![a, b, c, d, e, f] := by
  decide +kernel

theorem mIdx_mPt : ∀ i : Fin 36, mIdx (mPt i) = i := by
  decide +kernel

theorem polar_nondeg : ∀ a b c d e f : ZMod 2,
    (∀ a' b' c' d' e' f' : ZMod 2, polM ![a, b, c, d, e, f] ![a', b', c', d', e', f'] = 0) →
      ![a, b, c, d, e, f] = 0 := by
  decide +kernel

theorem qPt_mIdx_tM : ∀ i j : Fin 36, qPt (mIdx (tM (mPt i) (mPt j))) = rQ (qPt i) (qPt j) ∨
    qPt (mIdx (tM (mPt i) (mPt j))) = -rQ (qPt i) (qPt j) := by
  decide +kernel

end CFSG.Fischer.Classification.MinusFive
