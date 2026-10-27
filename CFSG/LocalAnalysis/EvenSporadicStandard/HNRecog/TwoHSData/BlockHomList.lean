module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockHom
public import Mathlib.Data.List.Forall2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private theorem label_perm_unique_list {α : Type*} {k : ℕ} (blk : α → Option (Fin k))
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

theorem exists_blockHom_list {α : Type*} {k : ℕ} (gs : List (Equiv.Perm α))
    (ps : List (Equiv.Perm (Fin k))) (blk : α → Option (Fin k))
    (hsurj : ∀ j : Fin k, ∃ p, blk p = some j)
    (h : List.Forall₂ (fun (g : Equiv.Perm α) (π : Equiv.Perm (Fin k)) =>
      ∀ p, blk (g p) = (blk p).map π) gs ps) :
    ∃ φ : ↥(closure {x | x ∈ gs}) →* Equiv.Perm (Fin k),
      (∀ (x : ↥(closure {x | x ∈ gs})) (p : α),
        blk ((x : Equiv.Perm α) p) = (blk p).map (φ x)) ∧
        φ.range = closure {x | x ∈ ps} := by
  classical
  have h' := h
  have hlen : gs.length = ps.length := h'.length_eq
  have hget : ∀ (i : Fin gs.length) (p : α),
      blk (gs.get i p) = (blk p).map (ps.get (Fin.cast hlen i)) := by
    intro i p
    have hval : i.val < ps.length := hlen ▸ i.isLt
    have hrel := h'.get (i := i.val) i.isLt hval
    simpa using hrel p
  let pi : Equiv.Perm α → Equiv.Perm (Fin k) := fun g =>
    if hg : ∃ i : Fin gs.length, gs.get i = g
    then ps.get (Fin.cast hlen (Classical.choose hg))
    else 1
  have hpi : ∀ g ∈ gs, ∀ p, blk (g p) = (blk p).map (pi g) := by
    intro g hg p
    have hex : ∃ i : Fin gs.length, gs.get i = g := List.mem_iff_get.mp hg
    have hpi_eq : pi g = ps.get (Fin.cast hlen (Classical.choose hex)) := by
      dsimp only [pi]
      rw [dif_pos hex]
    rw [hpi_eq]
    have hrel := hget (Classical.choose hex) p
    rw [Classical.choose_spec hex] at hrel
    exact hrel
  have himg : pi '' {x | x ∈ gs} = {x | x ∈ ps} := by
    apply Set.Subset.antisymm
    · rintro y ⟨g, hg, rfl⟩
      have hex : ∃ i : Fin gs.length, gs.get i = g := List.mem_iff_get.mp hg
      have hpi_eq : pi g = ps.get (Fin.cast hlen (Classical.choose hex)) := by
        dsimp only [pi]
        rw [dif_pos hex]
      rw [hpi_eq]
      exact List.get_mem ps _
    · intro y hy
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hy
      refine ⟨gs.get (Fin.cast hlen.symm j), List.get_mem gs _, ?_⟩
      have hex : ∃ m : Fin gs.length, gs.get m = gs.get (Fin.cast hlen.symm j) :=
        ⟨Fin.cast hlen.symm j, rfl⟩
      have hpi_eq : pi (gs.get (Fin.cast hlen.symm j))
          = ps.get (Fin.cast hlen (Classical.choose hex)) := by
        dsimp only [pi]
        rw [dif_pos hex]
      rw [hpi_eq, ← hj]
      apply label_perm_unique_list blk hsurj (x := gs.get (Fin.cast hlen.symm j))
      · intro p
        have hrel := hget (Classical.choose hex) p
        rw [Classical.choose_spec hex] at hrel
        exact hrel
      · intro p
        have hrel := hget (Fin.cast hlen.symm j) p
        have hcast : Fin.cast hlen (Fin.cast hlen.symm j) = j := Fin.ext rfl
        rw [hcast] at hrel
        exact hrel
  obtain ⟨φ, hφ, hφgen⟩ :=
    exists_blockHom (closure {x | x ∈ gs}) {x | x ∈ gs} rfl blk hsurj pi hpi
  exact ⟨φ, hφ, by rw [blockHom_range (closure {x | x ∈ gs}) {x | x ∈ gs} rfl φ pi hφgen, himg]⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
