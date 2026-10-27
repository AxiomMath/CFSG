module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpExt
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpSub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module

section Fix

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {E : Subgroup (W ≃ₗ[ZMod 2] W)} {n : ℕ} (D : PlaneData E n)

theorem PlaneData.piecesOf_stable (S : Set (Fin n)) (g : W ≃ₗ[ZMod 2] W) (hg : g ∈ E) :
    ∀ w ∈ D.piecesOf S, g w ∈ D.piecesOf S := by
  intro w hw
  refine D.piecesOf_induction (C := fun w => g w ∈ D.piecesOf S) ?_ ?_ ?_ w hw
  · simp
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro i hi x hx
    obtain ⟨k, hk⟩ := D.pow i g hg
    rw [hk x hx]
    exact le_biSup D.X hi (D.rho_pow_mem i (k : ℕ) x hx)

@[expose] def PlaneData.fixU : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {g | g ∈ E ∧ ∀ u ∈ D.piecesOf (idxLo n), g u = u}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨E.mul_mem ha hb, fun u hu => ?_⟩
    rw [LinearEquiv.mul_apply, hb' u hu, ha' u hu]
  one_mem' := ⟨E.one_mem, fun u _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨E.inv_mem ha, fun u hu => ?_⟩
    have h := ha' u hu
    calc a⁻¹ u = a⁻¹ (a u) := by rw [h]
      _ = u := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem PlaneData.e_mem_fixU (i : Fin n) (hi : 2 ≤ i.val) : D.e i ∈ D.fixU := by
  refine ⟨D.emem i, fun u hu => ?_⟩
  refine D.piecesOf_induction (C := fun u => D.e i u = u) ?_ ?_ ?_ u hu
  · simp
  · intro x y hx hy
    rw [map_add, hx, hy]
  · intro j hj x hx
    have hj' : j.val < 2 := hj
    have hne : i ≠ j := by
      intro h
      rw [h] at hi
      omega
    rw [D.eact i j x hx, if_neg (Ne.symm hne)]

theorem PlaneData.hi_mem_stable (g : W ≃ₗ[ZMod 2] W) (hg : g ∈ E) :
    ∀ w ∈ D.piecesOf (idxHi n), g w ∈ D.piecesOf (idxHi n) :=
  D.piecesOf_stable _ g hg

theorem PlaneData.extFun_comm (U Wc : Submodule (ZMod 2) W) (hc : IsCompl U Wc)
    (hUW : U = D.piecesOf (idxLo n)) (hWc : Wc = D.piecesOf (idxHi n)) (g : W ≃ₗ[ZMod 2] W)
    (hg : g ∈ D.fixU) (φ : U ≃ₗ[ZMod 2] U) :
    g * extFun U Wc hc φ = extFun U Wc hc φ * g := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, w, rfl⟩ := exists_decomp_compl U Wc hc v
  have hgu : g (u : W) = u := hg.2 u (hUW ▸ u.2)
  have hgw : g (w : W) ∈ Wc := by
    have hw : (w : W) ∈ D.piecesOf (idxHi n) := hWc ▸ w.2
    have := D.hi_mem_stable g hg.1 _ hw
    exact hWc ▸ this
  have hgφ : g ((φ u : U) : W) = ((φ u : U) : W) := hg.2 _ (hUW ▸ (φ u).2)
  show g (extFun U Wc hc φ ((u : W) + (w : W))) = extFun U Wc hc φ (g ((u : W) + (w : W)))
  rw [extFun_apply, map_add, map_add, hgu, hgφ]
  have key := extFun_apply U Wc hc φ u ⟨g (w : W), hgw⟩
  simp only at key
  rw [key]

end Fix

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
