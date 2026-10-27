module

public import CFSG.Sporadic.Schreier.ONPermArr
public import Mathlib.Data.Set.Card

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.ONSchreier

@[expose] def ptsSet (n : ℕ) (pts : Array ℕ) : Set (Fin n) :=
  {p | ∃ j < pts.size, pts[j]! = p.val}

theorem countP_range_eq_card (m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (List.range m).countP (fun i => decide (P i)) = ((Finset.range m).filter P).card := by
  rw [List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter, Multiset.range]

theorem countFix_eq {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g) :
    (List.range n).countP (fun i => t[i]! == i) = Set.ncard {p : Fin n | g p = p} := by
  have h1 : (List.range n).countP (fun i => t[i]! == i) =
      (List.range n).countP (fun i => decide (t[i]! = i)) := by
    congr 1
  rw [h1, countP_range_eq_card n (fun i => t[i]! = i)]
  have h2 : {p : Fin n | g p = p} = (fun i : Fin n => i.val) ⁻¹' ↑((Finset.range n).filter
      (fun i => t[i]! = i)) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.coe_filter, Finset.mem_range]
    constructor
    · intro h
      refine ⟨p.2, ?_⟩
      rw [ht p, h]
    · rintro ⟨-, h⟩
      apply Fin.ext
      rw [← h, ht p]
  rw [h2]
  have hsub : (↑((Finset.range n).filter (fun i => t[i]! = i)) : Set ℕ) ⊆ Set.range
      (fun i : Fin n => i.val) := by
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
    exact ⟨⟨x, hx.1⟩, rfl⟩
  rw [Set.ncard_preimage_of_injective_subset_range Fin.val_injective hsub, Set.ncard_coe_finset]

theorem countFixOn_eq {n : ℕ} {pts t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : PRep n t g)
    (hlt : ∀ j < pts.size, pts[j]! < n)
    (hinj : ∀ j < pts.size, ∀ j' < pts.size, pts[j]! = pts[j']! → j = j') :
    (List.range pts.size).countP (fun j => t[pts[j]!]! == pts[j]!) =
      Set.ncard {p : Fin n | p ∈ ptsSet n pts ∧ g p = p} := by
  have h1 : (List.range pts.size).countP (fun j => t[pts[j]!]! == pts[j]!) =
      (List.range pts.size).countP (fun j => decide (t[pts[j]!]! = pts[j]!)) := by
    congr 1
  rw [h1, countP_range_eq_card pts.size (fun j => t[pts[j]!]! = pts[j]!), ← Set.ncard_coe_finset]
  have hmem : ∀ j : ℕ, j ∈ (↑((Finset.range pts.size).filter (fun j => t[pts[j]!]! = pts[j]!)) :
      Set ℕ) → j < pts.size ∧ t[pts[j]!]! = pts[j]! := by
    intro j hj
    have := Finset.mem_coe.1 hj
    simpa using this
  refine Set.ncard_congr (fun j hj => (⟨pts[j]!, hlt j (hmem j hj).1⟩ : Fin n)) ?_ ?_ ?_
  · intro j hj
    have hj' := hmem j hj
    refine ⟨⟨j, hj'.1, rfl⟩, Fin.ext ?_⟩
    have := ht ⟨pts[j]!, hlt j hj'.1⟩
    simp only at this ⊢
    rw [← this, hj'.2]
  · intro j j' hj hj' h
    exact hinj j (hmem j hj).1 j' (hmem j' hj').1 (congrArg Fin.val h)
  · rintro p ⟨⟨j, hj, hjp⟩, hgp⟩
    have hlt' : pts[j]! < n := hlt j hj
    have hpe : p = ⟨pts[j]!, hlt'⟩ := Fin.ext hjp.symm
    have := ht ⟨pts[j]!, hlt'⟩
    have hg' : g ⟨pts[j]!, hlt'⟩ = ⟨pts[j]!, hlt'⟩ := by rw [← hpe]; exact hgp
    refine ⟨j, ?_, hpe.symm⟩
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨hj, ?_⟩
    rw [this, hg']

end CFSG.EvenSporadicStandard.Solomon78
