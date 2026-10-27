module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

@[expose] def certCheckWith (n m p : ℕ) (R Bcols Ecols Qcols : Array ℕ) : Bool :=
  bIsId n (bxor n (bmul n m (btr m n Bcols) (btr n m Ecols)) (bmul n p (btr p n Qcols) R))

@[expose] def injCheckWith (n p : ℕ) (R Qcols : Array ℕ) : Bool :=
  bIsId n (bmul n p (btr p n Qcols) R)

theorem exists_eq_mulVec_of_certCheckWith {n m p : ℕ} {R Bcols Ecols Qcols : Array ℕ}
    (h : certCheckWith n m p R Bcols Ecols Qcols = true) {c : Fin n → ZMod 2}
    (hc : toMat p n R *ᵥ c = 0) : ∃ e : Fin m → ZMod 2, c = (toMat m n Bcols)ᵀ *ᵥ e := by
  have h1 : toMat n m (btr m n Bcols) * toMat m n (btr n m Ecols) +
      toMat n p (btr p n Qcols) * toMat p n R = 1 := by
    rw [← toMat_bmul, ← toMat_bmul, ← toMat_bxor]
    exact toMat_eq_one_of_bIsId h
  refine ⟨toMat m n (btr n m Ecols) *ᵥ c, ?_⟩
  rw [← toMat_btr]
  exact eq_mulVec_of_cert h1 hc

theorem eq_zero_of_injCheckWith {n p : ℕ} {R Qcols : Array ℕ} (h : injCheckWith n p R Qcols = true)
    {c : Fin n → ZMod 2} (hc : toMat p n R *ᵥ c = 0) : c = 0 := by
  have h1 : toMat n p (btr p n Qcols) * toMat p n R = 1 := by
    rw [← toMat_bmul]
    exact toMat_eq_one_of_bIsId h
  exact eq_zero_of_cert h1 hc

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
