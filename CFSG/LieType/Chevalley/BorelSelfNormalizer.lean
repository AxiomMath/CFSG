module

public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.BruhatDecomposition

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem eq_one_of_canonicalRep_conj_posUnipotent_le
    {w : WeylGroup τ}
    (h : ∀ u ∈ posUnipotent τ K, canonicalRep (coxeterSystem τ) K w * u *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ borelGroup τ K) : w = 1 := by
  by_contra hw
  obtain ⟨i, hroot, hneg⟩ := (weyl_exchange_condition τ).2.2.2 w hw
  set n := canonicalRep (coxeterSystem τ) K w
  set x := pinnedX τ K (Pi.single i 1) 1
  have hx : x ∈ posUnipotent τ K :=
    Subgroup.mem_iSup_of_mem (Pi.single i 1) (Subgroup.mem_iSup_of_mem
      ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩
      (Subgroup.subset_closure ⟨1, rfl⟩))
  have hconj : n * x * n⁻¹ ∈ rootSubgroup τ K (w • Pi.single i 1) := by
    rw [← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ i)]
    exact ⟨x, Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
  have hneg' : n * x * n⁻¹ ∈ negUnipotent τ K :=
    Subgroup.mem_iSup_of_mem (w • Pi.single i 1) (Subgroup.mem_iSup_of_mem ⟨hroot, hneg⟩ hconj)
  have hmem : n * x * n⁻¹ ∈ borelGroup τ K ⊓ negUnipotent τ K :=
    Subgroup.mem_inf.2 ⟨h x hx, hneg'⟩
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left] at hmem
  have h01 : (1 : K) = 0 :=
    pinnedX_injective τ K (Pi.single i 1) (hmem.trans (pinnedX_zero τ K (Pi.single i 1)).symm)
  exact one_ne_zero h01

theorem mem_borelGroup_of_conj_posUnipotent_le
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (h : ∀ b ∈ borelGroup τ K, ∀ b' ∈ borelGroup τ K, ∀ w : WeylGroup τ,
      b * canonicalRep (coxeterSystem τ) K w * b' = g →
      ∀ u ∈ posUnipotent τ K, canonicalRep (coxeterSystem τ) K w * u *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ borelGroup τ K) :
    g ∈ borelGroup τ K := by
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  have hw1 := eq_one_of_canonicalRep_conj_posUnipotent_le (h b hb b' hb' w rfl)
  subst hw1
  rw [canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem borel_self_normalizers
    (τ : Tag) (K : Type) [Field K] :
    adjointGroup τ K ⊓ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) =
      borelGroup τ K ∧
    adjointGroup τ K ⊓ Subgroup.normalizer (borelGroup τ K : Set (ModGL τ K)) =
      borelGroup τ K := by
  have hBC : borelGroup τ K ≤ adjointGroup τ K :=
    ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  refine ⟨le_antisymm (fun g hg => ?_) (le_inf hBC hBN),
    le_antisymm (fun g hg => ?_) (le_inf hBC Subgroup.le_normalizer)⟩
  · obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
    refine mem_borelGroup_of_conj_posUnipotent_le hgC fun b hb b' hb' w hgw u hu => hUB ?_
    have hn : canonicalRep (coxeterSystem τ) K w = b⁻¹ * g * b'⁻¹ := by
      rw [← hgw]
      group
    have hnN : canonicalRep (coxeterSystem τ) K w ∈
        Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
      rw [hn]
      exact mul_mem (mul_mem (inv_mem (hBN hb)) hgN) (inv_mem (hBN hb'))
    exact (Subgroup.mem_normalizer_iff.1 hnN u).1 hu
  · obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
    refine mem_borelGroup_of_conj_posUnipotent_le hgC fun b hb b' hb' w hgw u hu => ?_
    have hn : canonicalRep (coxeterSystem τ) K w = b⁻¹ * g * b'⁻¹ := by
      rw [← hgw]
      group
    have hnN : canonicalRep (coxeterSystem τ) K w ∈
        Subgroup.normalizer (borelGroup τ K : Set (ModGL τ K)) := by
      rw [hn]
      exact mul_mem (mul_mem (inv_mem (Subgroup.le_normalizer hb)) hgN)
        (inv_mem (Subgroup.le_normalizer hb'))
    exact (Subgroup.mem_normalizer_iff.1 hnN u).1 (hUB hu)

end CFSG.LieType.Chevalley
