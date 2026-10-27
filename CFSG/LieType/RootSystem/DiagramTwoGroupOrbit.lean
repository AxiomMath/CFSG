module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
import CFSG.Mathlib.Combinatorics.SimpleGraph.TreeTwoGroupOrbit
import CFSG.Mathlib.GroupTheory.GroupAction.OrbitCardLeTwo
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.UniqueBranch
import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.NoBranch
import TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge

public section

namespace CFSG.LieType.RootSystem

variable {B : Type*} [Fintype B] [DecidableEq B] {A : Matrix B B ℤ}

private noncomputable def diagramSmul {G X C : Type*} [Group G] [MulAction G X] (f : C → X)
    (hrange : ∀ (g : G) (i : C), ∃ j, g • f i = f j) (g : G) (i : C) : C :=
  Classical.choose (hrange g i)

private lemma diagramSmul_spec {G X C : Type*} [Group G] [MulAction G X] (f : C → X)
    (hrange : ∀ (g : G) (i : C), ∃ j, g • f i = f j) (g : G) (i : C) :
    g • f i = f (diagramSmul f hrange g i) :=
  Classical.choose_spec (hrange g i)

@[instance_reducible]
private noncomputable def diagramMulAction {G X C : Type*} [Group G] [MulAction G X] (f : C → X)
    (hf : Function.Injective f)
    (hrange : ∀ (g : G) (i : C), ∃ j, g • f i = f j) : MulAction G C where
  smul := diagramSmul f hrange
  one_smul i := hf (by
    calc f (diagramSmul f hrange 1 i) = 1 • f i := (diagramSmul_spec f hrange 1 i).symm
      _ = f i := one_smul G (f i))
  mul_smul g₁ g₂ i := hf (by
    calc f (diagramSmul f hrange (g₁ * g₂) i)
        = (g₁ * g₂) • f i := (diagramSmul_spec f hrange (g₁ * g₂) i).symm
      _ = g₁ • (g₂ • f i) := mul_smul g₁ g₂ (f i)
      _ = g₁ • f (diagramSmul f hrange g₂ i) := by rw [diagramSmul_spec f hrange g₂ i]
      _ = f (diagramSmul f hrange g₁ (diagramSmul f hrange g₂ i)) :=
            diagramSmul_spec f hrange g₁ _)

theorem eq_of_degree_eq_three_of_isFiniteType (h : TauCeti.IsFiniteType A)
    (hconn : (TauCeti.diagramGraph A).Connected) {u v : B}
    (hu : (TauCeti.diagramGraph A).degree u = 3) (hv : (TauCeti.diagramGraph A).degree v = 3) :
    u = v := by
  by_cases h2 : ∃ i j, i ≠ j ∧ A i j * A j i = 2
  · obtain ⟨i, j, hij, hij2⟩ := h2
    have := h.degree_le_two_of_apply_mul_apply_eq_two hconn.preconnected hij2 u
    omega
  · by_cases h3 : ∃ i j, i ≠ j ∧ A i j * A j i = 3
    · obtain ⟨i, j, hij, hij3⟩ := h3
      have hcard := h.card_eq_two_of_apply_mul_apply_eq_three hconn.preconnected hij3
      have := (TauCeti.diagramGraph A).degree_lt_card_verts u
      omega
    · apply h.eq_of_degree_eq_three _ hconn hu hv
      rw [h.isSimplyLaced_iff]
      intro i j hij
      have hmem := h.apply_mul_apply_mem_of_ne hij
      have hne2 : A i j * A j i ≠ 2 := fun hc => h2 ⟨i, j, hij, hc⟩
      have hne3 : A i j * A j i ≠ 3 := fun hc => h3 ⟨i, j, hij, hc⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hh | hh | hh | hh <;> omega

theorem card_orbit_le_two_of_isFiniteType (h : TauCeti.IsFiniteType A)
    (hconn : (TauCeti.diagramGraph A).Connected) {G : Type*} [Group G] [Finite G]
    [MulAction G B] (hG : IsPGroup 2 G)
    (hadj : ∀ (g : G) (i j : B),
      (TauCeti.diagramGraph A).Adj (g • i) (g • j) ↔ (TauCeti.diagramGraph A).Adj i j)
    (i : B) : Nat.card (MulAction.orbit G i) ≤ 2 :=
  CFSG.Combinatorics.card_orbit_le_two_of_isTree (h.isTree_diagramGraph hconn)
    h.degree_le_three (fun _ _ => eq_of_degree_eq_three_of_isFiniteType h hconn) hG hadj i

theorem smul_eq_or_smul_eq_or_smul_eq_smul_of_isFiniteType (h : TauCeti.IsFiniteType A)
    (hconn : (TauCeti.diagramGraph A).Connected) {G X : Type*} [Group G] [Finite G]
    [MulAction G X] (hG : IsPGroup 2 G) {f : B → X} (hf : Function.Injective f)
    (hrange : ∀ (g : G) (i : B), ∃ j, g • f i = f j)
    (hadj : ∀ (g : G) (i j i' j' : B), g • f i = f i' → g • f j = f j' →
      ((TauCeti.diagramGraph A).Adj i' j' ↔ (TauCeti.diagramGraph A).Adj i j))
    (i : B) (g₁ g₂ : G) : g₁ • f i = f i ∨ g₂ • f i = f i ∨ g₁ • f i = g₂ • f i := by
  let : MulAction G B := diagramMulAction f hf hrange
  have hpres : ∀ (g : G) (i j : B),
      (TauCeti.diagramGraph A).Adj (g • i) (g • j) ↔ (TauCeti.diagramGraph A).Adj i j :=
    fun g i j => hadj g i j (g • i) (g • j)
      (diagramSmul_spec f hrange g i) (diagramSmul_spec f hrange g j)
  have hbound : Nat.card (MulAction.orbit G i) ≤ 2 :=
    card_orbit_le_two_of_isFiniteType h hconn hG hpres i
  rcases CFSG.smul_eq_or_smul_eq_or_smul_eq_smul_of_card_orbit_le_two hbound g₁ g₂ with
    hh | hh | hh
  · left
    rw [diagramSmul_spec f hrange g₁ i]
    exact congrArg f (show diagramSmul f hrange g₁ i = i from hh)
  · right; left
    rw [diagramSmul_spec f hrange g₂ i]
    exact congrArg f (show diagramSmul f hrange g₂ i = i from hh)
  · right; right
    rw [diagramSmul_spec f hrange g₁ i, diagramSmul_spec f hrange g₂ i]
    exact congrArg f
      (show diagramSmul f hrange g₁ i = diagramSmul f hrange g₂ i from hh)

end CFSG.LieType.RootSystem
