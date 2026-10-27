module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5ModData

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Equiv Matrix

theorem Mt_tri' : ∀ (g : A5) (p : Fin 15 × Fin 15), blk p.2 < blk p.1 → Mt g p.1 p.2 = 0 := by
  decide +kernel

theorem Mt_tri (g : A5) (l k : Fin 15) (h : blk k < blk l) : Mt g l k = 0 :=
  Mt_tri' g (l, k) h

theorem Mt_triv0 : ∀ g : A5, Mt g 0 0 = 1 := by decide +kernel
theorem Mt_triv2 : ∀ g : A5, Mt g 5 5 = 1 := by decide +kernel
theorem Mt_triv3 : ∀ g : A5, Mt g 6 6 = 1 := by decide +kernel

def SimpleBlk (ρ : A5 → Fin 4 → Fin 4 → ZMod 2) : Prop :=
  ∀ x f : Fin 4 → ZMod 2, x ≠ 0 → f ≠ 0 → ∃ g : A5, ∑ l, f l * ∑ k, ρ g l k * x k = 1

instance (ρ : A5 → Fin 4 → Fin 4 → ZMod 2) : Decidable (SimpleBlk ρ) := by
  unfold SimpleBlk; infer_instance

theorem simple1 : SimpleBlk (bm 1) := by decide +kernel
theorem simple4 : SimpleBlk (bm 7) := by decide +kernel
theorem simple5 : SimpleBlk (bm 11) := by decide +kernel

theorem om1_comm : ∀ g : A5, ∀ l k : Fin 4, ∑ t, om1 l t * bm 1 g t k = ∑ t, bm 1 g l t * om1 t k := by
  decide +kernel

theorem om4_comm : ∀ g : A5, ∀ l k : Fin 4, ∑ t, om4 l t * bm 7 g t k = ∑ t, bm 7 g l t * om4 t k := by
  decide +kernel

theorem om1_sq : ∀ l k : Fin 4, ∑ t, om1 l t * om1 t k + om1 l k + (if l = k then 1 else 0) = 0 := by
  decide +kernel

theorem om4_sq : ∀ l k : Fin 4, ∑ t, om4 l t * om4 t k + om4 l k + (if l = k then 1 else 0) = 0 := by
  decide +kernel

theorem bm5_eq_Dm : ∀ g : A5, ∀ l k : Fin 4, bm 11 g l k = Dm g l k := by decide +kernel

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
