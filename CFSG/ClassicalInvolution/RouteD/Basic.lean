module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {B : Type} [Fintype B]

@[expose] def stdCartan (t : DynkinType) : Matrix (Fin t.rank) (Fin t.rank) ℤ :=
  t.cartanMatrix.transpose

theorem stdCartan_apply (t : DynkinType) (i j : Fin t.rank) :
    stdCartan t i j = t.cartanMatrix j i := rfl

omit [Fintype B] in
theorem diagramGraph_transpose (A : Matrix B B ℤ) :
    diagramGraph A.transpose = diagramGraph A := by
  ext i j
  simp only [diagramGraph_adj, Matrix.transpose_apply]
  tauto

theorem classify {Γ : Matrix B B ℤ} (h : IsFiniteType Γ) (hc : (diagramGraph Γ).Connected) :
    ∃ t : DynkinType, t.Valid ∧ ∃ e : B ≃ Fin t.rank, ∀ x y, Γ x y = stdCartan t (e x) (e y) := by
  have hc' : (diagramGraph Γ.transpose).Connected := by rwa [diagramGraph_transpose]
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ := h.transpose.existsUnique_dynkinType hc'
  exact ⟨t, ht, e, fun x y => by simpa [stdCartan_apply] using he y x⟩

theorem stdCartan_A (n : ℕ) (i j : Fin n) : stdCartan (.A n) i j = CartanMatrix.A n j i :=
  congrFun (congrFun (DynkinType.cartanMatrix_A n) j) i

theorem stdCartan_B (n : ℕ) (i j : Fin n) : stdCartan (.B n) i j = CartanMatrix.B n j i :=
  congrFun (congrFun (DynkinType.cartanMatrix_B n) j) i

theorem stdCartan_C (n : ℕ) (i j : Fin n) : stdCartan (.C n) i j = CartanMatrix.C n j i :=
  congrFun (congrFun (DynkinType.cartanMatrix_C n) j) i

theorem stdCartan_D (n : ℕ) (i j : Fin n) : stdCartan (.D n) i j = CartanMatrix.D n j i :=
  congrFun (congrFun (DynkinType.cartanMatrix_D n) j) i

theorem stdCartan_E6 (i j : Fin 6) : stdCartan .E6 i j = CartanMatrix.E 6 j i :=
  congrFun (congrFun DynkinType.cartanMatrix_E6 j) i

theorem stdCartan_E7 (i j : Fin 7) : stdCartan .E7 i j = CartanMatrix.E 7 j i :=
  congrFun (congrFun DynkinType.cartanMatrix_E7 j) i

theorem stdCartan_E8 (i j : Fin 8) : stdCartan .E8 i j = CartanMatrix.E 8 j i :=
  congrFun (congrFun DynkinType.cartanMatrix_E8 j) i

theorem stdCartan_F4 (i j : Fin 4) : stdCartan .F4 i j = CartanMatrix.F₄ j i :=
  congrFun (congrFun DynkinType.cartanMatrix_F4 j) i

theorem stdCartan_G2 (i j : Fin 2) : stdCartan .G2 i j = CartanMatrix.G₂ i j :=
  congrFun (congrFun DynkinType.cartanMatrix_G2 j) i

end CFSG.ClassicalInvolution.RouteD
