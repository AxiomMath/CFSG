module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2PermSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Data.L34Outer

public section

namespace CFSG.AGLEmbedding.L34Outer

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.AGLEmbedding.FusD2 Certificates.L34Outer

@[expose] def g4 : List (Equiv.Perm (Fin 42)) := [g₁, g₂, g₃, g₄]

@[expose] def g6 : List (Equiv.Perm (Fin 42)) := [g₁, g₂, g₃, g₄, g₅, g₆]

@[expose] def L34T : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure {g₁, g₂, g₃, g₄}

theorem g4_mem_T : ∀ g ∈ g4, g ∈ L34T := by
  intro g hg
  simp only [g4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)

theorem g6_mem_R : ∀ g ∈ g6, g ∈ R := by
  intro g hg
  simp only [g6, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)

theorem wordVal_g4_mem (w : List ℤ) : wordVal g4 w ∈ L34T := wordVal_mem g4 L34T g4_mem_T w

theorem wordVal_g6_mem (w : List ℤ) : wordVal g6 w ∈ R := wordVal_mem g6 R g6_mem_R w

theorem S_le_T : S ≤ L34T := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl <;> simp

theorem T_le_R : L34T ≤ R := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> simp

@[expose] def Psub (D : Data) : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure {g | g ∈ [D.a, D.b].map (wordVal g4)}

@[expose] def Esub (e : EData) : Subgroup (Equiv.Perm (Fin 42)) :=
  Subgroup.closure {g | g ∈ [e.u, e.v].map (wordVal g4)}

@[expose] def zel (D : Data) : Equiv.Perm (Fin 42) := wordVal g4 D.z

theorem Psub_le_T (D : Data) : Psub D ≤ L34T := by
  unfold Psub
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordVal_g4_mem w

structure OuterFacts (D : Data) : Prop where
  cardT : Nat.card L34T = 60480
  order3 : ∀ r ∈ R, r ^ 3 = 1 → r ∈ L34T
  cardP : Nat.card (Psub D) = 27
  P_le_T : Psub D ≤ L34T
  noncomm : wordVal g4 D.a * wordVal g4 D.b ≠ wordVal g4 D.b * wordVal g4 D.a
  pairs : ∀ x ∈ Psub D, ∀ y ∈ Psub D, Nat.card (Subgroup.closure {x, y}) = 9 →
    ∃ e ∈ D.es, Subgroup.closure {x, y} = Esub e
  inS : ∀ e ∈ D.es, e.inS = true → Esub e ≤ S
  z_ne : zel D ≠ 1
  z_mem : ∀ e ∈ D.es, zel D ∈ Esub e
  exhibit : ∀ e ∈ D.es, e.inS = false → ∃ L : List (Equiv.Perm (Fin 42)),
    (∀ h ∈ L, h ∈ L34T ∧ ∃ y ∈ Esub e, y ≠ 1 ∧
      h ∈ Subgroup.normalizer (Subgroup.zpowers y : Set (Equiv.Perm (Fin 42)))) ∧
    Subgroup.closure {h | h ∈ L} = L34T
  extras : ∃ X : List (Equiv.Perm (Fin 42)),
    (∀ x ∈ X, x ∈ R ∧
      x ∈ Subgroup.normalizer (Subgroup.zpowers (zel D) : Set (Equiv.Perm (Fin 42)))) ∧
    ∀ r ∈ R, r ∈ L34T ∨ ∃ x ∈ X, x⁻¹ * r ∈ L34T

end CFSG.AGLEmbedding.L34Outer
