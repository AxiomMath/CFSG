module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighType

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh.D4K

open CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def oD4 : List (List ℤ) :=
  [[-1, -2, -1, -1], [-1, 0, 0, 0], [-1, -1, -1, 0], [0, 0, -1, 0], [1, 2, 1, 1], [1, 0, 0, 0],
   [1, 1, 1, 0], [0, 0, 1, 0], [1, 1, 1, 1], [1, 1, 0, 0], [0, 1, 1, 0], [-1, -1, -1, -1],
   [-1, -1, 0, 0], [0, -1, -1, 0], [-1, -1, 0, -1], [0, -1, -1, -1], [0, -1, 0, 0], [1, 1, 0, 1],
   [0, 1, 1, 1], [0, 1, 0, 0], [0, 1, 0, 1], [0, -1, 0, -1], [0, 0, 0, -1], [0, 0, 0, 1]]

@[expose] def f02 : List (List ℤ) :=
  [[-1, -1, 0, -1], [-1, 0, 0, 0], [-1, -1, 0, 0], [0, -1, -1, -1], [1, 0, 0, 0], [1, 1, 0, 1],
   [0, -1, -1, 0], [1, 1, 0, 0], [0, 1, 1, 1], [0, 0, -1, 0], [0, 1, 1, 0], [0, 0, 1, 0],
   [1, 2, 1, 1], [1, 1, 1, 0], [-1, -1, -1, -1], [0, -1, 0, 0], [-1, -2, -1, -1], [-1, -1, -1, 0],
   [0, 1, 0, 1], [1, 1, 1, 1], [0, 1, 0, 0], [0, 0, 0, -1], [0, -1, 0, -1], [0, 0, 0, 1]]

@[expose] def f03 : List (List ℤ) :=
  [[1, 2, 1, 1], [1, 1, 0, 1], [-1, -1, -1, -1], [0, -1, 0, 0], [-1, -2, -1, -1], [-1, -1, 0, -1],
   [0, 1, 1, 0], [1, 1, 1, 1], [0, 1, 0, 0], [0, 0, -1, 0], [0, -1, -1, 0], [0, 0, 1, 0],
   [-1, -1, -1, 0], [-1, 0, 0, 0], [-1, -1, 0, 0], [0, -1, -1, -1], [1, 0, 0, 0], [1, 1, 1, 0],
   [0, -1, 0, -1], [1, 1, 0, 0], [0, 1, 1, 1], [0, 0, 0, -1], [0, 1, 0, 1], [0, 0, 0, 1]]

@[expose] def f23 : List (List ℤ) :=
  [[1, 2, 1, 1], [1, 1, 0, 0], [0, -1, 0, 0], [-1, -1, -1, -1], [-1, -2, -1, -1], [-1, 0, 0, 0],
   [0, 1, 1, 1], [1, 1, 1, 1], [1, 0, 0, 0], [0, -1, -1, -1], [-1, -1, 0, 0], [0, 1, 0, 0],
   [-1, -1, -1, 0], [0, -1, -1, 0], [-1, -1, 0, -1], [0, 0, -1, 0], [0, 0, 1, 0], [1, 1, 1, 0],
   [0, -1, 0, -1], [0, 0, 0, -1], [0, 1, 0, 1], [0, 1, 1, 0], [1, 1, 0, 1], [0, 0, 0, 1]]

theorem iter2_fix {α : Type*} (f : α → α) (g : ℕ → α) (hg : ∀ k, g (k + 1) = f (g k)) (x : α)
    (k0 : ℕ) (h0 : g k0 = x) (hx : f (f x) = x) : ∀ m, g (k0 + 2 * m) = x
  | 0 => h0
  | m + 1 => by
    have e : k0 + 2 * (m + 1) = k0 + 2 * m + 1 + 1 := by omega
    rw [e, hg, hg, iter2_fix f g hg x k0 h0 hx m, hx]

theorem orbitIter_D4_six : orbitIter (CartanMatrix.D 4) 6 = oD4 := by decide +kernel

theorem orbitStep_oD4 :
    orbitStep (CartanMatrix.D 4) (orbitStep (CartanMatrix.D 4) oD4) = oD4 := by
  decide +kernel

theorem orbitIter_D4 : orbitIter (CartanMatrix.D 4) 30 = oD4 :=
  iter2_fix (orbitStep (CartanMatrix.D 4)) (orbitIter (CartanMatrix.D 4)) (fun _ => rfl) oD4 6
    orbitIter_D4_six orbitStep_oD4 12

theorem closedB_oD4 : closedB (CartanMatrix.D 4) oD4 = true := by decide +kernel

@[expose] def foldStep (a b : Fin 4) (L : List (List ℤ)) : List (List ℤ) :=
  (L ++ L.flatMap (foldMoves (CartanMatrix.D 4) a b)).dedup

theorem foldIter_D4_02_four : foldIter (CartanMatrix.D 4) (0 : Fin 4) (2 : Fin 4) 4 = f02 := by
  decide +kernel

theorem foldStep_f02 : foldStep 0 2 (foldStep 0 2 f02) = f02 := by decide +kernel

theorem foldIter_D4_02 : foldIter (CartanMatrix.D 4) (0 : Fin 4) (2 : Fin 4) 30 = f02 :=
  iter2_fix (foldStep 0 2) (foldIter (CartanMatrix.D 4) 0 2) (fun _ => rfl) f02 4
    foldIter_D4_02_four foldStep_f02 13

theorem foldIter_D4_03_four : foldIter (CartanMatrix.D 4) (0 : Fin 4) (3 : Fin 4) 4 = f03 := by
  decide +kernel

theorem foldStep_f03 : foldStep 0 3 (foldStep 0 3 f03) = f03 := by decide +kernel

theorem foldIter_D4_03 : foldIter (CartanMatrix.D 4) (0 : Fin 4) (3 : Fin 4) 30 = f03 :=
  iter2_fix (foldStep 0 3) (foldIter (CartanMatrix.D 4) 0 3) (fun _ => rfl) f03 4
    foldIter_D4_03_four foldStep_f03 13

theorem foldIter_D4_23_four : foldIter (CartanMatrix.D 4) (2 : Fin 4) (3 : Fin 4) 4 = f23 := by
  decide +kernel

theorem foldStep_f23 : foldStep 2 3 (foldStep 2 3 f23) = f23 := by decide +kernel

theorem foldIter_D4_23 : foldIter (CartanMatrix.D 4) (2 : Fin 4) (3 : Fin 4) 30 = f23 :=
  iter2_fix (foldStep 2 3) (foldIter (CartanMatrix.D 4) 2 3) (fun _ => rfl) f23 4
    foldIter_D4_23_four foldStep_f23 13

end CFSG.LocalAnalysis.GLTheoremA.T171Sh.D4K

end
