module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairFlipSet

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace PairFlip

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tp_eq_swap (i : ι) (b : Bool) : tp i = swap (i, b) (i, !b) := by
  unfold tp
  cases b
  · simp [swap_comm]
  · simp

open scoped Classical in
@[expose] noncomputable def outSet (W : Subgroup (Perm (ι × Bool))) : Finset ι :=
  Finset.univ.filter fun i => tp i ∉ W

theorem mem_outSet {W : Subgroup (Perm (ι × Bool))} {i : ι} : i ∈ outSet W ↔ tp i ∉ W := by
  simp [outSet]

theorem exists_mem_flip {W : Subgroup (Perm (ι × Bool))}
    (hD : ∀ i j, i ≠ j → tp i ∉ W → tp j ∉ W → tp i * tp j ∈ W)
    (hT1 : (outSet W).card ≠ 1) (z : ι × Bool) : ∃ w ∈ W, w z = (z.1, !z.2) := by
  obtain ⟨i, b⟩ := z
  by_cases hi : tp i ∈ W
  · exact ⟨tp i, hi, by rw [tp_apply]; simp⟩
  · have hiT : i ∈ outSet W := mem_outSet.2 hi
    have hgt : 1 < (outSet W).card := by
      have := Finset.card_pos.2 ⟨i, hiT⟩
      omega
    obtain ⟨j, hjT, hji⟩ := Finset.exists_mem_ne hgt i
    refine ⟨tp i * tp j, hD i j hji.symm hi (mem_outSet.1 hjT), ?_⟩
    have h1 : tp j (i, b) = (i, b) := by rw [tp_apply]; simp [hji.symm]
    rw [Perm.mul_apply, h1, tp_apply]
    simp

theorem normalizer_flip {W : Subgroup (Perm (ι × Bool))} (hle : W ≤ J0 ι)
    (hD : ∀ i j, i ≠ j → tp i ∉ W → tp j ∉ W → tp i * tp j ∈ W)
    (hT1 : (outSet W).card ≠ 1) {g : Perm (ι × Bool)} (hg : g ∈ Subgroup.normalizer (W : Set _))
    (z : ι × Bool) : g (z.1, !z.2) = ((g z).1, !(g z).2) := by
  obtain ⟨w, hw, hwz⟩ := exists_mem_flip hD hT1 z
  have hw' : g * w * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hg w).1 hw
  rcases mem_J0.1 (hle hw') (g z) with e | e
  · exfalso
    have : g (w z) = g z := by simpa using e
    have := g.injective this
    rw [hwz] at this
    have h2 := congrArg Prod.snd this
    simp at h2
  · simpa [hwz] using e

theorem normalizer_fst {W : Subgroup (Perm (ι × Bool))} (hle : W ≤ J0 ι)
    (hD : ∀ i j, i ≠ j → tp i ∉ W → tp j ∉ W → tp i * tp j ∈ W)
    (hT1 : (outSet W).card ≠ 1) {g : Perm (ι × Bool)} (hg : g ∈ Subgroup.normalizer (W : Set _))
    (i : ι) (b : Bool) : g * tp i * g⁻¹ = tp (g (i, b)).1 := by
  have hflip := normalizer_flip hle hD hT1 hg
  have h1 : g * tp i * g⁻¹ = swap (g (i, b)) (g (i, !b)) := by
    rw [tp_eq_swap i b, ← swap_apply_apply]
  rw [h1]
  have h2 : g (i, !b) = ((g (i, b)).1, !(g (i, b)).2) := hflip (i, b)
  rw [h2]
  exact (tp_eq_swap _ _).symm

theorem normalizer_mem_outSet {W : Subgroup (Perm (ι × Bool))} (hle : W ≤ J0 ι)
    (hD : ∀ i j, i ≠ j → tp i ∉ W → tp j ∉ W → tp i * tp j ∈ W)
    (hT1 : (outSet W).card ≠ 1) {g : Perm (ι × Bool)} (hg : g ∈ Subgroup.normalizer (W : Set _))
    (z : ι × Bool) : z.1 ∈ outSet W ↔ (g z).1 ∈ outSet W := by
  have h := normalizer_fst hle hD hT1 hg z.1 z.2
  rw [mem_outSet, mem_outSet, ← h]
  have := Subgroup.mem_normalizer_iff.1 hg (tp z.1)
  rw [Iff.not this]

theorem conj_mem_J0 {u : Perm (ι × Bool)} (hu : ∀ z, u (z.1, !z.2) = ((u z).1, !(u z).2))
    {w : Perm (ι × Bool)} (hw : w ∈ J0 ι) : u * w * u⁻¹ ∈ J0 ι := by
  refine mem_J0.2 fun z => ?_
  have hz : u (u⁻¹ z) = z := by simp
  have hexp : (u * w * u⁻¹) z = u (w (u⁻¹ z)) := rfl
  rcases mem_J0.1 hw (u⁻¹ z) with e | e
  · left; rw [hexp, e, hz]
  · right; rw [hexp, e, hu, hz]

end PairFlip

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
