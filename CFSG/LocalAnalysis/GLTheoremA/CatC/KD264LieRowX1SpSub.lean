module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpPlanes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
variable {E : Subgroup (W ≃ₗ[ZMod 2] W)} {n : ℕ} (D : PlaneData E n)

@[expose] def idxLo (n : ℕ) : Set (Fin n) := {i | i.val < 2}

@[expose] def idxHi (n : ℕ) : Set (Fin n) := {i | 2 ≤ i.val}

@[expose] def PlaneData.piecesOf (S : Set (Fin n)) : Submodule (ZMod 2) W := ⨆ i ∈ S, D.X i

theorem PlaneData.piecesOf_induction {S : Set (Fin n)} {C : W → Prop} (h0 : C 0)
    (hadd : ∀ x y, C x → C y → C (x + y)) (hi : ∀ i ∈ S, ∀ x ∈ D.X i, C x) :
    ∀ x ∈ D.piecesOf S, C x := by
  intro x hx
  refine Submodule.iSup_induction (fun i => ⨆ (_ : i ∈ S), D.X i) (motive := C) hx ?_ h0 hadd
  intro i y hy
  by_cases hiS : i ∈ S
  · rw [iSup_pos hiS] at hy
    exact hi i hiS y hy
  · rw [iSup_neg hiS] at hy
    rw [Submodule.mem_bot] at hy
    rw [hy]
    exact h0

theorem PlaneData.orth_piecesOf (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) {S T : Set (Fin n)}
    (hST : ∀ i ∈ S, ∀ j ∈ T, i ≠ j) :
    ∀ x ∈ D.piecesOf S, ∀ y ∈ D.piecesOf T, f x y = 0 := by
  intro x hx
  refine D.piecesOf_induction (C := fun x => ∀ y ∈ D.piecesOf T, f x y = 0) ?_ ?_ ?_ x hx
  · intro y _
    simp
  · intro x x' hx hx' y hy
    rw [map_add, LinearMap.add_apply, hx y hy, hx' y hy, add_zero]
  · intro i hi x hx y hy
    refine D.piecesOf_induction (C := fun y => f x y = 0) ?_ ?_ ?_ y hy
    · simp
    · intro y y' hy hy'
      rw [map_add, hy, hy', add_zero]
    · intro j hj y hy
      exact D.orth_of_ne f hf (hST i hi j hj) hx hy

theorem sym_of_alt (f : LinearMap.BilinForm (ZMod 2) W) (hf : f.IsAlt) (x y : W) :
    f x y = f y x := by
  have h := hf (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  have hx := hf x
  have hy := hf y
  rw [hx, hy] at h
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  simp only [zero_add, add_zero] at h
  exact (key _ _ h).symm

theorem PlaneData.piecesOf_lo (hn : 2 ≤ n) :
    D.piecesOf (idxLo n) = D.X ⟨0, by omega⟩ ⊔ D.X ⟨1, by omega⟩ := by
  apply le_antisymm
  · refine iSup_le (fun i => iSup_le (fun hi => ?_))
    have hi' : (i : Fin n).val < 2 := hi
    rcases (show (i : Fin n).val = 0 ∨ (i : Fin n).val = 1 by omega) with h | h
    · have : i = ⟨0, by omega⟩ := Fin.ext h
      rw [this]; exact le_sup_left
    · have : i = ⟨1, by omega⟩ := Fin.ext h
      rw [this]; exact le_sup_right
  · refine sup_le ?_ ?_
    · exact le_biSup D.X (show (⟨0, by omega⟩ : Fin n) ∈ idxLo n from by
        show (0 : ℕ) < 2; omega)
    · exact le_biSup D.X (show (⟨1, by omega⟩ : Fin n) ∈ idxLo n from by
        show (1 : ℕ) < 2; omega)

theorem PlaneData.inf_lo (hn : 2 ≤ n) : D.X ⟨0, by omega⟩ ⊓ D.X ⟨1, by omega⟩ = ⊥ := by
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  exact (D.indep.pairwiseDisjoint hne).eq_bot

theorem PlaneData.finrank_lo (hn : 2 ≤ n) :
    Module.finrank (ZMod 2) (D.piecesOf (idxLo n)) = 4 := by
  rw [D.piecesOf_lo hn]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (D.X ⟨0, by omega⟩) (D.X ⟨1, by omega⟩)
  rw [D.inf_lo hn, finrank_bot, D.dim2, D.dim2] at h
  omega

theorem PlaneData.isCompl_pieces (hn : 2 ≤ n) :
    IsCompl (D.piecesOf (idxLo n)) (D.piecesOf (idxHi n)) := by
  refine ⟨?_, ?_⟩
  · have hdisj : Disjoint (idxLo n) (idxHi n) := by
      rw [Set.disjoint_left]
      intro i hi hi'
      have h1 : (i : Fin n).val < 2 := hi
      have h2 : 2 ≤ (i : Fin n).val := hi'
      omega
    exact D.indep.disjoint_biSup_biSup' hdisj (Set.toFinite _)
  · rw [codisjoint_iff, eq_top_iff]
    rw [← D.sup_eq]
    refine iSup_le (fun i => ?_)
    by_cases hi : (i : Fin n).val < 2
    · exact le_sup_of_le_left (le_biSup D.X (show i ∈ idxLo n from hi))
    · exact le_sup_of_le_right (le_biSup D.X (show i ∈ idxHi n from by
        show 2 ≤ (i : Fin n).val; omega))

theorem PlaneData.orth_lo_hi (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) :
    ∀ u ∈ D.piecesOf (idxLo n), ∀ w ∈ D.piecesOf (idxHi n), f u w = 0 :=
  D.orth_piecesOf f hf (fun i hi j hj hij => by
    have h1 : i.val < 2 := hi
    have h2 : 2 ≤ j.val := hj
    exact absurd (congrArg Fin.val hij) (by omega))

theorem PlaneData.mem_lo_of_perp_hi (f : LinearMap.BilinForm (ZMod 2) W)
    (hf : ∀ g ∈ E, ∀ x y, f (g x) (g y) = f x y) (hfalt : f.IsAlt) (hfnd : f.Nondegenerate)
    (hn : 2 ≤ n) {v : W} (hv : ∀ w ∈ D.piecesOf (idxHi n), f v w = 0) :
    v ∈ D.piecesOf (idxLo n) := by
  have hcomp := D.isCompl_pieces hn
  have htop : ∀ z : W, z ∈ D.piecesOf (idxLo n) ⊔ D.piecesOf (idxHi n) := by
    intro z
    rw [hcomp.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (htop v)
  have hww : ∀ w' ∈ D.piecesOf (idxHi n), f w w' = 0 := by
    intro w' hw'
    have h := hv w' hw'
    rw [map_add, LinearMap.add_apply, D.orth_lo_hi f hf u hu w' hw', zero_add] at h
    exact h
  have hwU : ∀ x ∈ D.piecesOf (idxLo n), f w x = 0 := by
    intro x hx
    rw [sym_of_alt f hfalt]
    exact D.orth_lo_hi f hf x hx w hw
  have hw0 : w = 0 := by
    refine hfnd.1 w (fun z => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (htop z)
    rw [map_add, hwU a ha, hww b hb, zero_add]
  rw [hw0, add_zero]
  exact hu

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
