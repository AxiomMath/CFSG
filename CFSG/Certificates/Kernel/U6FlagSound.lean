module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagData
public import Certificates.Data.Kernel.U6.F2K

public section

namespace CFSG.KC.U6F2

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bxor)
open CFSG.EvenSmallLie.UnitarySix.YamadaN2 (msum2 blk2Bits emb2Bits par640)

theorem foldl_congr_range {α : Type} {n : ℕ} {f g : α → ℕ → α} (init : α)
    (h : ∀ a, ∀ i < n, f a i = g a i) :
    (List.range n).foldl f init = (List.range n).foldl g init := by
  have : ∀ (L : List ℕ) (b : α), (∀ i ∈ L, i < n) → L.foldl f b = L.foldl g b := by
    intro L
    induction L with
    | nil => intro b _; rfl
    | cons a L ih =>
      intro b hL
      simp only [List.foldl_cons]
      rw [h b a (hL a (List.mem_cons_self ..)), ih _ fun i hi => hL i (List.mem_cons_of_mem _ hi)]
  exact this _ _ fun i hi => List.mem_range.mp hi

end CFSG.KC.U6F2

end
