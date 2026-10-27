module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpSub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {E : Subgroup (W ≃ₗ[ZMod 2] W)} {n : ℕ} (D : PlaneData E n)

theorem PlaneData.piece_stable (hE : IsElemAbelian 3 E) (i : Fin n) (g : W ≃ₗ[ZMod 2] W)
    (hcomm : ∀ v, g (D.e i v) = D.e i (g v)) : ∀ x ∈ D.X i, g x ∈ D.X i := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := D.exists_pre hE i x hx
  rw [← hyx, map_sub, hcomm]
  exact D.range_sub i (g y)

theorem PlaneData.hi_stable (hE : IsElemAbelian 3 E) (g : W ≃ₗ[ZMod 2] W)
    (hcomm : ∀ i : Fin n, 2 ≤ i.val → ∀ v, g (D.e i v) = D.e i (g v)) :
    ∀ w ∈ D.piecesOf (idxHi n), g w ∈ D.piecesOf (idxHi n) := by
  intro w hw
  refine D.piecesOf_induction (C := fun w => g w ∈ D.piecesOf (idxHi n)) ?_ ?_ ?_ w hw
  · simp
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro i hi x hx
    have hi' : 2 ≤ i.val := hi
    exact le_biSup D.X hi (D.piece_stable hE i g (hcomm i hi') x hx)

theorem PlaneData.lo_stable (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hfnd : f.Nondegenerate)
    (hn : 2 ≤ n) (g : W ≃ₗ[ZMod 2] W) (hgf : ∀ x y, f (g x) (g y) = f x y)
    (hW : ∀ w ∈ D.piecesOf (idxHi n), g.symm w ∈ D.piecesOf (idxHi n)) :
    ∀ u ∈ D.piecesOf (idxLo n), g u ∈ D.piecesOf (idxLo n) := by
  intro u hu
  refine D.mem_lo_of_perp_hi f hf hfalt hfnd hn (fun w hw => ?_)
  have h1 : f (g u) w = f (g u) (g (g.symm w)) := by
    rw [LinearEquiv.apply_symm_apply]
  rw [h1, hgf, D.orth_lo_hi f hf u hu _ (hW w hw)]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
