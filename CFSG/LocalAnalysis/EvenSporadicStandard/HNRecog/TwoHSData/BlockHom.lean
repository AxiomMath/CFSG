module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

variable {α : Type*} {k : ℕ}

local instance instCoeFunSubgroupPerm (X : Subgroup (Equiv.Perm α)) :
    CoeFun X (fun _ => α → α) := ⟨fun x => (x : Equiv.Perm α)⟩

private theorem label_perm_unique (blk : α → Option (Fin k))
    (hsurj : ∀ j : Fin k, ∃ p, blk p = some j) {x : Equiv.Perm α}
    {π π' : Equiv.Perm (Fin k)}
    (h : ∀ p, blk (x p) = (blk p).map π) (h' : ∀ p, blk (x p) = (blk p).map π') :
    π = π' := by
  apply Equiv.Perm.ext
  intro j
  obtain ⟨p, hp⟩ := hsurj j
  have key : (blk p).map π = (blk p).map π' := by rw [← h p, ← h' p]
  rw [hp] at key
  exact Option.some.inj key

private theorem option_map_map_apply (π σ : Equiv.Perm (Fin k)) (o : Option (Fin k)) :
    (o.map σ).map π = o.map (π * σ) := by
  cases o with
  | none => rfl
  | some j => simp [Equiv.Perm.mul_apply]

private theorem option_map_inv_apply (π : Equiv.Perm (Fin k)) (o : Option (Fin k)) :
    (o.map π).map π.symm = o := by
  cases o with
  | none => rfl
  | some j => simp

private def labelSubgroup (blk : α → Option (Fin k)) : Subgroup (Equiv.Perm α) where
  carrier := {x | ∃ π : Equiv.Perm (Fin k), ∀ p, blk (x p) = (blk p).map π}
  one_mem' := ⟨1, fun p => by simp⟩
  mul_mem' := by
    rintro x y ⟨πx, hx⟩ ⟨πy, hy⟩
    refine ⟨πx * πy, fun p => ?_⟩
    rw [Equiv.Perm.mul_apply, hx (y p), hy p, option_map_map_apply]
  inv_mem' := by
    rintro x ⟨π, hπ⟩
    refine ⟨π⁻¹, fun p => ?_⟩
    have h : blk p = (blk (x⁻¹ p)).map π := by
      simpa using hπ (x⁻¹ p)
    calc blk (x⁻¹ p) = ((blk (x⁻¹ p)).map π).map π.symm := (option_map_inv_apply π _).symm
      _ = (blk p).map π.symm := by rw [← h]

theorem exists_blockHom (X : Subgroup (Equiv.Perm α)) (gens : Set (Equiv.Perm α))
    (hX : X = closure gens) (blk : α → Option (Fin k))
    (hsurj : ∀ j : Fin k, ∃ p, blk p = some j)
    (π : Equiv.Perm α → Equiv.Perm (Fin k))
    (hπ : ∀ g ∈ gens, ∀ p, blk (g p) = (blk p).map (π g)) :
    ∃ φ : X →* Equiv.Perm (Fin k),
      (∀ (x : X) (p : α), blk (x p) = (blk p).map (φ x)) ∧
        ∀ (x : X), (x : Equiv.Perm α) ∈ gens → φ x = π x := by
  have hXS : X ≤ labelSubgroup blk := by
    rw [hX, Subgroup.closure_le]
    exact fun g hg => ⟨π g, hπ g hg⟩
  let ψ : X → Equiv.Perm (Fin k) :=
    fun x => Classical.choose (show ∃ π : Equiv.Perm (Fin k), ∀ p, blk (x p) = (blk p).map π
      from hXS x.2)
  have ψspec : ∀ (x : X) (p : α), blk (x p) = (blk p).map (ψ x) :=
    fun x => Classical.choose_spec (show ∃ π : Equiv.Perm (Fin k),
      ∀ p, blk (x p) = (blk p).map π from hXS x.2)
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · refine label_perm_unique blk hsurj (x := (1 : Equiv.Perm α)) (π := ψ 1) (π' := 1) ?_ ?_
    · simpa using ψspec 1
    · intro p; simp
  · intro x y
    refine label_perm_unique blk hsurj (x := ((x * y : X) : Equiv.Perm α))
      (π := ψ (x * y)) (π' := ψ x * ψ y) ?_ ?_
    · exact ψspec (x * y)
    · intro p
      rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, ψspec x (y p), ψspec y p,
        option_map_map_apply]
  · exact ψspec
  · intro x hx
    exact label_perm_unique blk hsurj (x := (x : Equiv.Perm α)) (ψspec x) (hπ (x : Equiv.Perm α) hx)

theorem blockHom_eq_one_iff (blk : α → Option (Fin k)) (hsurj : ∀ j : Fin k, ∃ p, blk p = some j)
    {X : Subgroup (Equiv.Perm α)} (φ : X →* Equiv.Perm (Fin k))
    (hφ : ∀ (x : X) (p : α), blk (x p) = (blk p).map (φ x)) (x : X) :
    φ x = 1 ↔ ∀ p, blk (x p) = blk p := by
  constructor
  · intro h p
    rw [hφ x p, h]
    simp
  · intro h
    apply Equiv.Perm.ext
    intro j
    obtain ⟨p, hp⟩ := hsurj j
    have key := hφ x p
    rw [h p] at key
    rw [hp] at key
    exact (Option.some.inj key).symm

theorem blockHom_range (X : Subgroup (Equiv.Perm α)) (gens : Set (Equiv.Perm α))
    (hX : X = closure gens) (φ : X →* Equiv.Perm (Fin k))
    (π : Equiv.Perm α → Equiv.Perm (Fin k))
    (hφ : ∀ (x : X), (x : Equiv.Perm α) ∈ gens → φ x = π x) :
    φ.range = closure (π '' gens) := by
  apply le_antisymm
  · have key : ∀ g (hg : g ∈ closure gens) (h : g ∈ X),
        φ ⟨g, h⟩ ∈ closure (π '' gens) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        intro h
        rw [hφ ⟨g, h⟩ hg]
        exact Subgroup.subset_closure ⟨g, hg, rfl⟩
      | one =>
        intro h
        rw [show φ ⟨1, h⟩ = 1 from map_one φ]
        exact one_mem _
      | mul x y hx hy ihx ihy =>
        intro h
        have heq : (⟨x * y, h⟩ : X) = ⟨x, hX.symm ▸ hx⟩ * ⟨y, hX.symm ▸ hy⟩ :=
          Subtype.ext rfl
        rw [heq, map_mul]
        exact mul_mem (ihx (hX.symm ▸ hx)) (ihy (hX.symm ▸ hy))
      | inv x hx ihx =>
        intro h
        have heq : (⟨x⁻¹, h⟩ : X) = (⟨x, hX.symm ▸ hx⟩ : X)⁻¹ := Subtype.ext rfl
        rw [heq, map_inv]
        exact inv_mem (ihx (hX.symm ▸ hx))
    rintro _ ⟨x, rfl⟩
    exact key x.1 (hX ▸ x.2) x.2
  · rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨⟨g, hX.symm ▸ Subgroup.subset_closure hg⟩,
      hφ ⟨g, hX.symm ▸ Subgroup.subset_closure hg⟩ hg⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
