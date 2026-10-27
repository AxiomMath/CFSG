module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44GolayBlocks

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.EvenSporadicStandard.Wong77.Module

@[expose] def colAt (l : List ℕ) (p : Fin 23) : ℕ := l.getD p.val 0

@[expose] def initCol (D : Finset (Fin 23)) : List ℕ :=
  (List.finRange 23).map fun p => if p ∈ D then p.val else 23

theorem colAt_initCol (D : Finset (Fin 23)) (p : Fin 23) :
    colAt (initCol D) p = if p ∈ D then p.val else 23 := by
  simp [colAt, initCol, List.getD_eq_getElem?_getD]

@[expose] def blockCol (l : List ℕ) (B : Finset (Fin 23)) : ℕ := ∑ y ∈ B, 8 ^ colAt l y

@[expose] def refineCol (l : List ℕ) (p : Fin 23) : ℕ × Multiset ℕ :=
  (colAt l p, ((golayBlocks.filter fun B => p ∈ B).map (blockCol l) : List ℕ))

@[expose] def stepCol (l : List ℕ) : List ℕ :=
  let r := (List.finRange 23).map (refineCol l)
  r.map fun x => r.findIdx fun y => decide (y = x)

theorem colAt_stepCol (l : List ℕ) (p : Fin 23) :
    colAt (stepCol l) p = ((List.finRange 23).map (refineCol l)).findIdx
      fun y => decide (y = refineCol l p) := by
  simp [colAt, stepCol, List.getD_eq_getElem?_getD]

theorem colAt_stepCol_congr {l : List ℕ} {p q : Fin 23} (h : refineCol l p = refineCol l q) :
    colAt (stepCol l) p = colAt (stepCol l) q := by
  rw [colAt_stepCol, colAt_stepCol, h]

theorem blockCol_image {l : List ℕ} {g : Equiv.Perm (Fin 23)}
    (hl : ∀ p, colAt l (g p) = colAt l p) (B : Finset (Fin 23)) :
    blockCol l (B.image g) = blockCol l B := by
  rw [blockCol, Finset.sum_image (fun x _ y _ h => g.injective h)]
  simp only [hl]
  rfl

theorem refineCol_perm {l : List ℕ} {g : Equiv.Perm (Fin 23)} (hg : g ∈ permStab golayCode)
    (hl : ∀ p, colAt l (g p) = colAt l p) (p : Fin 23) :
    refineCol l (g p) = refineCol l p := by
  have hperm : (golayBlocks.filter fun B => g p ∈ B).Perm
      ((golayBlocks.filter fun B => p ∈ B).map (Finset.image g)) := by
    rw [List.perm_ext_iff_of_nodup (golayBlocks_nodup.filter _)
      ((golayBlocks_nodup.filter _).map (Finset.image_injective g.injective))]
    intro B'
    simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨hB', hp⟩
      refine ⟨B'.image ⇑g⁻¹, ⟨image_mem_golayBlocks ((permStab golayCode).inv_mem hg) hB', ?_⟩, ?_⟩
      · rw [Finset.mem_image]
        exact ⟨g p, hp, by simp⟩
      · rw [Finset.image_image]
        simp
    · rintro ⟨B, ⟨hB, hp⟩, rfl⟩
      exact ⟨image_mem_golayBlocks hg hB, Finset.mem_image_of_mem g hp⟩
  refine Prod.ext (hl p) ?_
  change (↑((golayBlocks.filter fun B => g p ∈ B).map (blockCol l)) : Multiset ℕ) =
    ↑((golayBlocks.filter fun B => p ∈ B).map (blockCol l))
  rw [Multiset.coe_eq_coe]
  have h := hperm.map (blockCol l)
  have h' : ((golayBlocks.filter fun B => p ∈ B).map (Finset.image g)).map (blockCol l) =
      (golayBlocks.filter fun B => p ∈ B).map (blockCol l) := by
    rw [List.map_map]
    exact List.map_congr_left fun B _ => blockCol_image hl B
  rwa [h'] at h

theorem colAt_stepCol_perm {l : List ℕ} {g : Equiv.Perm (Fin 23)} (hg : g ∈ permStab golayCode)
    (hl : ∀ p, colAt l (g p) = colAt l p) (p : Fin 23) :
    colAt (stepCol l) (g p) = colAt (stepCol l) p :=
  colAt_stepCol_congr (refineCol_perm hg hl p)

theorem colAt_initCol_perm {D : Finset (Fin 23)} {g : Equiv.Perm (Fin 23)}
    (hD : ∀ d ∈ D, g d = d) (p : Fin 23) : colAt (initCol D) (g p) = colAt (initCol D) p := by
  rw [colAt_initCol, colAt_initCol]
  by_cases hp : p ∈ D
  · rw [hD p hp]
  · have hgp : g p ∉ D := fun h => hp (by rwa [g.injective (hD _ h)] at h)
    simp [hp, hgp]

end CFSG.EvenSporadicStandard.TwoFi22.DS81
