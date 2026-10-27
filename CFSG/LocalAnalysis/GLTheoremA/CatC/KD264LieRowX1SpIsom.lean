module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpExt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpSub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module

section Isom

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {E : Subgroup (W ≃ₗ[ZMod 2] W)} {n : ℕ} (D : PlaneData E n)

@[expose] noncomputable def PlaneData.fU (f : LinearMap.BilinForm (ZMod 2) W) :
    LinearMap.BilinForm (ZMod 2) ↥(D.piecesOf (idxLo n)) :=
  f.compl₁₂ (D.piecesOf (idxLo n)).subtype (D.piecesOf (idxLo n)).subtype

theorem PlaneData.fU_apply (f : LinearMap.BilinForm (ZMod 2) W) (u v : ↥(D.piecesOf (idxLo n))) :
    D.fU f u v = f u v :=
  rfl

theorem PlaneData.fU_isAlt (f : LinearMap.BilinForm (ZMod 2) W) (hfalt : f.IsAlt) :
    (D.fU f).IsAlt := by
  intro u
  rw [PlaneData.fU_apply]
  exact hfalt u

theorem PlaneData.fU_nondeg (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hfnd : f.Nondegenerate)
    (hn : 2 ≤ n) : (D.fU f).Nondegenerate := by
  have hleft : ∀ u : ↥(D.piecesOf (idxLo n)), (∀ v, D.fU f u v = 0) → u = 0 := by
    intro u hu
    apply Subtype.ext
    refine hfnd.1 (u : W) (fun z => ?_)
    have hcomp := D.isCompl_pieces hn
    have htop : z ∈ D.piecesOf (idxLo n) ⊔ D.piecesOf (idxHi n) := by
      rw [hcomp.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 htop
    rw [map_add, D.orth_lo_hi f hf _ u.2 b hb, add_zero]
    have := hu ⟨a, ha⟩
    rw [PlaneData.fU_apply] at this
    exact this
  refine ⟨hleft, fun v hv => ?_⟩
  have hsym : ∀ u v : ↥(D.piecesOf (idxLo n)), D.fU f u v = D.fU f v u := by
    intro u v
    rw [PlaneData.fU_apply, PlaneData.fU_apply]
    exact sym_of_alt f hfalt _ _
  exact hleft v (fun u => by rw [hsym]; exact hv u)

theorem PlaneData.extFun_isom (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hn : 2 ≤ n)
    (φ : ↥(D.piecesOf (idxLo n)) ≃ₗ[ZMod 2] ↥(D.piecesOf (idxLo n)))
    (hφ : ∀ u v : ↥(D.piecesOf (idxLo n)), f (φ u : W) (φ v : W) = f u v) (x y : W) :
    f (extFun _ _ (D.isCompl_pieces hn) φ x) (extFun _ _ (D.isCompl_pieces hn) φ y) = f x y := by
  have hcomp := D.isCompl_pieces hn
  obtain ⟨a, b, rfl⟩ := exists_decomp_compl _ _ hcomp x
  obtain ⟨c, d, rfl⟩ := exists_decomp_compl _ _ hcomp y
  have hoff1 : ∀ u : ↥(D.piecesOf (idxLo n)), ∀ w : ↥(D.piecesOf (idxHi n)),
      f (u : W) (w : W) = 0 := fun u w => D.orth_lo_hi f hf u u.2 w w.2
  have hoff2 : ∀ u : ↥(D.piecesOf (idxLo n)), ∀ w : ↥(D.piecesOf (idxHi n)),
      f (w : W) (u : W) = 0 := fun u w => by
    rw [sym_of_alt f hfalt]
    exact hoff1 u w
  rw [extFun_apply, extFun_apply]
  simp only [map_add, LinearMap.add_apply, hφ, hoff1, hoff2, add_zero, zero_add]

end Isom

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
