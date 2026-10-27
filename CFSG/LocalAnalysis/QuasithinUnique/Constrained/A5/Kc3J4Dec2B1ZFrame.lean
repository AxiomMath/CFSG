module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZFrameNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZRows


public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

@[expose] noncomputable def zCj (t : J) : ℕ → J
  | 0 => t
  | n + 1 => fiveElt * zCj t n * fiveElt⁻¹

theorem zCj_eq (t : J) (n : ℕ) : zCj t n = fiveElt ^ n * t * (fiveElt ^ n)⁻¹ := by
  induction n with
  | zero => simp [zCj]
  | succ n ih =>
    rw [zCj, ih, pow_succ']
    group

theorem zCj_zero (t : J) : zCj t 0 = t := rfl

theorem zCj_one (t : J) : zCj t 1 = fiveElt * t * fiveElt⁻¹ := rfl

theorem zCj_two (t : J) : zCj t 2 = fiveElt ^ 2 * t * (fiveElt ^ 2)⁻¹ := zCj_eq t 2

theorem zCj_three (t : J) : zCj t 3 = fiveElt ^ 3 * t * (fiveElt ^ 3)⁻¹ := zCj_eq t 3

theorem Mx_zCj
    (hM : MatFacts) {t : J} {T : Array V2} (hT : Mx t = rowsMatrix T) (n : ℕ) :
    Mx (zCj t n) = rowsMatrix (zCjRows T n) := by
  induction n with
  | zero => exact hT
  | succ n ih =>
    unfold zCj zCjRows zXiConj
    rw [map_mul, map_mul, ih, Mx_fiveElt hM, Mx_fiveElt_inv hM, rowsMatrix_mulRows,
      rowsMatrix_mulRows]
    rfl

theorem zProdRows_eq : ∀ l : List (Array V2), zProdRows l = prodRows l
  | [] => rfl
  | r :: rs => by
    unfold zProdRows prodRows
    rw [zProdRows_eq rs]

end CFSG.QuasithinUnique.A5
