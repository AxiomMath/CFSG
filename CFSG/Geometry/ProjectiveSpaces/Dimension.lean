module

public import Mathlib.Order.Fin.Basic
public import CFSG.Geometry.ProjectiveSpaces.Basic

public section

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u

variable {P : Type u} (G : ProjectiveSpace P)

@[expose] def IsSubspaceChain (n : ℕ) (S : Fin (n + 1) → Set P) : Prop :=
  (∀ i, G.IsSubspace (S i) ∧ (S i).Nonempty) ∧ StrictMono S ∧ S (Fin.last n) = Set.univ

@[expose] def HasDimension (n : ℕ) : Prop :=
  (∃ S, G.IsSubspaceChain n S) ∧ ∀ m S, G.IsSubspaceChain m S → m ≤ n

theorem eq_plane_of_subset {x y z : P} (h : ¬ G.Collinear x y z) {T : Set P}
    (hT : G.IsSubspace T) (hTπ : T ⊆ G.plane x y z) {a b c : P} (ha : a ∈ T) (hb : b ∈ T)
    (hc : c ∈ T) (habc : ¬ G.Collinear a b c) : T = G.plane x y z := by
  refine hTπ.antisymm ?_
  rw [← G.plane_eq_of_mem h (hTπ ha) (hTπ hb) (hTπ hc) habc]
  exact G.plane_subset hT ha hb hc

theorem not_isSubspaceChain_three_of_plane_eq_univ {x y z : P} (h : ¬ G.Collinear x y z)
    (hπ : G.plane x y z = Set.univ) (S : Fin 4 → Set P)
    (hS : ∀ i, G.IsSubspace (S i) ∧ (S i).Nonempty) (hmono : StrictMono S) : False := by
  obtain ⟨x₀, hx₀⟩ := (hS 0).2
  have h01 : S 0 < S 1 := hmono (by decide)
  have h12 : S 1 < S 2 := hmono (by decide)
  have h23 : S 2 < S 3 := hmono (by decide)
  obtain ⟨x₁, hx₁, hx₁0⟩ := Set.exists_of_ssubset h01
  obtain ⟨x₂, hx₂, hx₂1⟩ := Set.exists_of_ssubset h12
  have hx₀₁ : x₀ ≠ x₁ := fun e => hx₁0 (e ▸ hx₀)
  have hline : G.line x₀ x₁ ⊆ S 1 := (hS 1).1.line_subset (h01.le hx₀) hx₁
  have hcol : ¬ G.Collinear x₀ x₁ x₂ := fun h' =>
    hx₂1 (hline ((G.collinear_iff_of_ne hx₀₁).1 h'))
  have hS2 : S 2 = G.plane x y z :=
    G.eq_plane_of_subset h (hS 2).1 (hπ ▸ Set.subset_univ _) (h12.le (h01.le hx₀))
      (h12.le hx₁) hx₂ hcol
  have := h23.2
  exact this (hS2 ▸ hπ ▸ Set.subset_univ _)

theorem exists_not_mem_plane {n : ℕ} (hn : 3 ≤ n) (hG : G.HasDimension n) {x y z : P}
    (h : ¬ G.Collinear x y z) : ∃ w, w ∉ G.plane x y z := by
  by_contra hall
  push Not at hall
  have hπ : G.plane x y z = Set.univ := Set.eq_univ_of_forall hall
  obtain ⟨S, hS, hmono, -⟩ := hG.1
  let f : Fin 4 → Fin (n + 1) := fun i => ⟨i, by omega⟩
  have hf : StrictMono f := fun i j hij => by
    change (i : ℕ) < (j : ℕ)
    exact hij
  exact G.not_isSubspaceChain_three_of_plane_eq_univ h hπ (S ∘ f) (fun i => hS (f i))
    (hmono.comp hf)

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
