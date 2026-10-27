module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.CPrime

@[expose] def snoc7 {α : Type*} (f : Fin 6 → α) (x : α) : Fin 7 → α :=
  fun i => if h : (i : ℕ) < 6 then f ⟨i, h⟩ else x

@[expose] def splitPr (ε : Eps) : Fin 7 → Array ℕ :=
  snoc7 (fun i => genRows ε i) (reflRows ε (n0 ε))

@[expose] def splitUr (ε : Eps) : Fin 7 → Array ℕ :=
  snoc7 (fun k => Stage2.urRows ε k) (reflRows ε (n0 ε))

theorem snoc7_lt {α : Type*} (f : Fin 6 → α) (x : α) (i : Fin 6) :
    snoc7 f x ⟨i, by omega⟩ = f i := by
  simp [snoc7]

theorem snoc7_six {α : Type*} (f : Fin 6 → α) (x : α) : snoc7 f x 6 = x := by
  simp [snoc7]

end CFSG.EvenSmallLie.OmegaEight.N3Split
