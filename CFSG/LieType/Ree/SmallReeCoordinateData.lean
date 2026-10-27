module

public import CFSG.LieType.Ree.SmallReeCollection
public import CFSG.LieType.Chevalley.RootCommutatorReduction

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def smallReeSigma (a : ℕ) {K : Type*} [CommRing K] (x : K) : K :=
  x ^ (3 * 3 ^ a)

@[expose] def smallReeCoord
    (a : ℕ) (K : Type*) [CommRing K] (t b c : K) :
    (Module.End K (RootModule Tag.G2 K))ˣ :=
  smallReeX K 0 t * smallReeX K 1 (smallReeSigma a t) * smallReeX K 2 b * smallReeX K 3 c *
    smallReeX K 4 (smallReeSigma a b - t ^ 3 * smallReeSigma a t) *
    smallReeX K 5 (smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2)

theorem smallReeRoot_check : ∀ i : Fin 6,
    RootOps.isRootB Tag.G2 (smallReeRoot i) = true ∧ 0 < height (smallReeRoot i) := by
  decide +kernel

theorem smallReeX_mem_posUnipotent
    (K : Type*) [CommRing K] (i : Fin 6) (c : K) :
    smallReeX K i c ∈ posUnipotent Tag.G2 K :=
  (le_iSup₂_of_le (smallReeRoot i) ⟨RootOps.isRootB_iff.1 (smallReeRoot_check i).1,
      (smallReeRoot_check i).2⟩ le_rfl : rootSubgroup Tag.G2 K (smallReeRoot i) ≤ _)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem smallReeCoord_mem_posUnipotent
    (a : ℕ) (K : Type*) [CommRing K] (t b c : K) :
    smallReeCoord a K t b c ∈ posUnipotent Tag.G2 K := by
  unfold smallReeCoord
  refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact smallReeX_mem_posUnipotent K _ _

end CFSG.LieType.Ree
