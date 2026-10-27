module

public import CFSG.LieType.Chevalley.D4TripleA2Lemmas

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley Matrix
open scoped commutatorElement

abbrev d4Node (a : ℕ) (h : a < 4 := by decide) : Fin Tag.D4.rank := ⟨a, h⟩

@[expose] def d4TripleA
    (R : Type*) [CommRing R] (i : Fin Tag.D4.rank) (c : R) :
    (Module.End R (RootModule .D4 R))ˣ :=
  weylElt .D4 R i (-1) * xUnit .D4 R (d4Node 2) c * weylElt .D4 R i 1

variable {R : Type*} [CommRing R]

theorem d4_commute_of_rootForm_nonneg
    {α β : Fin Tag.D4.rank → ℤ} (hα : IsRoot .D4 α)
    (hβ : IsRoot .D4 β) (hne : α ≠ β) (h0 : 0 ≤ α ⬝ᵥ (Tag.D4.symmetrizedCartan *ᵥ β))
    {x y : (Module.End R (RootModule .D4 R))ˣ} (hx : x ∈ rootSubgroup .D4 R α)
    (hy : y ∈ rootSubgroup .D4 R β) : Commute x y :=
  rootSubgroup_commute_of_rootForm_nonneg (Or.inl rfl) hα hβ hne h0 hx hy

theorem d4_cartan_outer (i : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) :
    Tag.D4.cartan i (d4Node 2) = -1 ∧ Tag.D4.cartan (d4Node 2) i = -1 := by
  revert i
  decide

theorem d4_reflect_outer (i : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) :
    reflect .D4 i (Pi.single (d4Node 2) 1) = Pi.single i 1 + Pi.single (d4Node 2) 1 := by
  revert i
  decide

theorem d4_isRoot_outer (i : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) :
    IsRoot .D4 (Pi.single i 1 + Pi.single (d4Node 2) 1) :=
  d4_reflect_outer i hi ▸ IsRoot.reflect i (isRoot_single _ _)

theorem d4TripleA_mem_rootSubgroup
    (i : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) (c : R) :
    d4TripleA R i c ∈ rootSubgroup .D4 R (Pi.single i 1 + Pi.single (d4Node 2) 1) := by
  rw [← d4_reflect_outer i hi, d4TripleA, ← weylElt_inv]
  exact weylElt_inv_conj_mem_rootSubgroup i (isRoot_single _ _) (xUnit_mem_rootSubgroup _ c)

theorem d4_commutator_yUnit_d4TripleA
    (i : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) (c : R) :
    ⁅yUnit .D4 R i (-1), d4TripleA R i c⁆ = xUnit .D4 R (d4Node 2) c := by
  obtain ⟨h1, h2⟩ := d4_cartan_outer i hi
  have h := commutatorElement_yUnit_weylConj (R := R) h1 h2 1 c
  rwa [one_mul] at h

theorem d4_commute_yUnit_d4TripleA
    (i j : Fin Tag.D4.rank) (hi : i ≠ d4Node 2)
    (hj : j ≠ d4Node 2) (hij : i ≠ j) (c : R) :
    Commute (yUnit .D4 R i (-1)) (d4TripleA R j c) :=
  d4_commute_of_rootForm_nonneg (isRoot_neg_single _ i) (d4_isRoot_outer j hj)
    (by revert i j; decide) (by revert i j; decide) (yUnit_mem_rootSubgroup i _)
    (d4TripleA_mem_rootSubgroup j hj c)

theorem d4_commute_yUnit_xUnit
    (i : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) (c : R) :
    Commute (yUnit .D4 R i (-1)) (xUnit .D4 R (d4Node 2) c) :=
  d4_commute_of_rootForm_nonneg (isRoot_neg_single _ i) (isRoot_single _ _)
    (by revert i; decide) (by revert i; decide) (yUnit_mem_rootSubgroup i _)
    (xUnit_mem_rootSubgroup _ c)

theorem d4_commute_d4TripleA_xUnit
    (i : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) (c d : R) :
    Commute (d4TripleA R i c) (xUnit .D4 R (d4Node 2) d) :=
  d4_commute_of_rootForm_nonneg (d4_isRoot_outer i hi) (isRoot_single _ _)
    (by revert i; decide) (by revert i; decide) (d4TripleA_mem_rootSubgroup i hi c)
    (xUnit_mem_rootSubgroup _ d)

theorem d4_commute_yUnit_yUnit
    (i j : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) (hj : j ≠ d4Node 2) :
    Commute (yUnit .D4 R i (-1)) (yUnit .D4 R j (-1)) := by
  by_cases hij : i = j
  · rw [hij]
  exact d4_commute_of_rootForm_nonneg (isRoot_neg_single _ i) (isRoot_neg_single _ j)
    (by revert i j; decide) (by revert i j; decide) (yUnit_mem_rootSubgroup i _)
    (yUnit_mem_rootSubgroup j _)

theorem d4_commute_d4TripleA_d4TripleA
    (i j : Fin Tag.D4.rank) (hi : i ≠ d4Node 2)
    (hj : j ≠ d4Node 2) (c : R) : Commute (d4TripleA R i c) (d4TripleA R j c) := by
  by_cases hij : i = j
  · rw [hij]
  exact d4_commute_of_rootForm_nonneg (d4_isRoot_outer i hi) (d4_isRoot_outer j hj)
    (by revert i j; decide) (by revert i j; decide) (d4TripleA_mem_rootSubgroup i hi c)
    (d4TripleA_mem_rootSubgroup j hj c)

theorem d4_triple_a2_commutator
    (R : Type*) [CommRing R] (c : R) :
    ⁅yUnit .D4 R (d4Node 0) (-1) * yUnit .D4 R (d4Node 1) (-1) * yUnit .D4 R (d4Node 3) (-1),
        d4TripleA R (d4Node 0) c * d4TripleA R (d4Node 1) c * d4TripleA R (d4Node 3) c⁆ =
      xUnit .D4 R (d4Node 2) (3 * c) ∧
    (∀ i : Fin Tag.D4.rank, i ≠ d4Node 2 →
      d4TripleA R i c ∈ rootSubgroup .D4 R (Pi.single i 1 + Pi.single (d4Node 2) 1)) ∧
    ∀ i j : Fin Tag.D4.rank, i ≠ d4Node 2 → j ≠ d4Node 2 →
      Commute (yUnit .D4 R i (-1)) (yUnit .D4 R j (-1)) ∧
        Commute (d4TripleA R i c) (d4TripleA R j c) := by
  refine ⟨?_, fun i hi => d4TripleA_mem_rootSubgroup i hi c, fun i j hi hj =>
    ⟨d4_commute_yUnit_yUnit i j hi hj, d4_commute_d4TripleA_d4TripleA i j hi hj c⟩⟩
  have h0 : d4Node 0 ≠ d4Node 2 := by decide
  have h1 : d4Node 1 ≠ d4Node 2 := by decide
  have h3 : d4Node 3 ≠ d4Node 2 := by decide
  have cyA := fun (i j : Fin Tag.D4.rank) (hi : i ≠ d4Node 2) (hj : j ≠ d4Node 2) (hij : i ≠ j) =>
    d4_commute_yUnit_d4TripleA (R := R) i j hi hj hij c
  have inner : ⁅yUnit .D4 R (d4Node 1) (-1) * yUnit .D4 R (d4Node 3) (-1),
      d4TripleA R (d4Node 1) c * d4TripleA R (d4Node 3) c⁆ =
        xUnit .D4 R (d4Node 2) c * xUnit .D4 R (d4Node 2) c := by
    rw [commutatorElement_mul_mul (cyA _ _ h3 h1 (by decide)) (cyA _ _ h1 h3 (by decide))
        (by rw [d4_commutator_yUnit_d4TripleA _ h3]; exact d4_commute_yUnit_xUnit _ h1 c)
        (by rw [d4_commutator_yUnit_d4TripleA _ h3]; exact d4_commute_d4TripleA_xUnit _ h1 c c),
      d4_commutator_yUnit_d4TripleA _ h1, d4_commutator_yUnit_d4TripleA _ h3]
  have hy0 : Commute (yUnit .D4 R (d4Node 0) (-1)) ⁅yUnit .D4 R (d4Node 1) (-1) *
      yUnit .D4 R (d4Node 3) (-1), d4TripleA R (d4Node 1) c * d4TripleA R (d4Node 3) c⁆ := by
    rw [inner]
    exact (d4_commute_yUnit_xUnit _ h0 c).mul_right (d4_commute_yUnit_xUnit _ h0 c)
  have hA0 : Commute (d4TripleA R (d4Node 0) c) ⁅yUnit .D4 R (d4Node 1) (-1) *
      yUnit .D4 R (d4Node 3) (-1), d4TripleA R (d4Node 1) c * d4TripleA R (d4Node 3) c⁆ := by
    rw [inner]
    exact (d4_commute_d4TripleA_xUnit _ h0 c c).mul_right (d4_commute_d4TripleA_xUnit _ h0 c c)
  rw [mul_assoc (yUnit .D4 R (d4Node 0) (-1)), mul_assoc (d4TripleA R (d4Node 0) c),
    commutatorElement_mul_mul ((cyA _ _ h1 h0 (by decide)).mul_left (cyA _ _ h3 h0 (by decide)))
      ((cyA _ _ h0 h1 (by decide)).mul_right (cyA _ _ h0 h3 (by decide))) hy0 hA0,
    inner, d4_commutator_yUnit_d4TripleA _ h0, ← xUnit_add, ← xUnit_add]
  congr 1
  ring

end CFSG.LieType.Chevalley
