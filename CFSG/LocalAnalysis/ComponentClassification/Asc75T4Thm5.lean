module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Hyp61

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.Open (aschbacherThm5Core aschbacherThm5OddCore aschbacherThm5Preimage
  aschbacherThm5Centralizes aschbacherThm5IsSemisimple)

variable {G : Type} [Group G] [Finite G]

@[expose] def Theorem5Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Subgroup G) (r : ℕ)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)),
    Hyp61 G D r Abar → normalizer (D : Set G) ≠ ⊤ → Conclusion G D r Abar

noncomputable def linkedFinset (Q : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite (linkedClass Q)).toFinset

theorem mem_linkedFinset {Q A : Subgroup G} : A ∈ linkedFinset Q ↔ A ∈ linkedClass Q :=
  Set.Finite.mem_toFinset _

noncomputable def linkedEnum (Q : Subgroup G) (i : Fin (linkedFinset Q).card) : Subgroup G :=
  ((linkedFinset Q).equivFin.symm i : Subgroup G)

theorem linkedEnum_mem (Q : Subgroup G) (i : Fin (linkedFinset Q).card) :
    linkedEnum Q i ∈ linkedClass Q :=
  mem_linkedFinset.mp ((linkedFinset Q).equivFin.symm i).2

theorem linkedEnum_injective (Q : Subgroup G) : Function.Injective (linkedEnum Q) :=
  fun _ _ h => (linkedFinset Q).equivFin.symm.injective (Subtype.ext h)

theorem exists_linkedEnum_eq {Q A : Subgroup G} (hA : A ∈ linkedClass Q) :
    ∃ i, linkedEnum Q i = A :=
  ⟨(linkedFinset Q).equivFin ⟨A, mem_linkedFinset.mpr hA⟩, by simp [linkedEnum]⟩

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem hyp61 (hN : NormalInConjNormalizer Q) :
    Hyp61 G (linkedLayer Q) (linkedFinset Q).card
      (fun i => layerBar (linkedLayer Q) (linkedEnum Q i)) where
  hr := Finset.card_pos.mpr ⟨Q, mem_linkedFinset.mpr (self_mem_linkedClass Q)⟩
  hdistinct := fun i j h => linkedEnum_injective Q
    (hS.eq_of_layerBar_eq (linkedEnum_mem Q i) (linkedEnum_mem Q j) h)
  hsemisimple := fun i => hS.aschbacherThm5IsSemisimple_layerBar (linkedEnum_mem Q i)
  hcomm := fun i j hij => hS.commute_layerBar (linkedEnum_mem Q i) (linkedEnum_mem Q j)
    fun h => hij (linkedEnum_injective Q h)
  hgen := iSup_layerBar_eq_top (linkedEnum Q) fun _ hA => exists_linkedEnum_eq hA
  hperm := fun h hh i => by
    obtain ⟨j, hj⟩ := exists_linkedEnum_eq
      (hS.rightConjugate_mem_linkedClass_of_mem_normalizer (inv_mem hh) (linkedEnum_mem Q i))
    exact ⟨j, by rw [hS.map_preimage_layerBar hh (linkedEnum_mem Q i), hj]⟩
  hi := fun i j _ _ htwo hZ hti htj =>
    hS.mem_normalizer_of_centralizes_fusion (linkedEnum_mem Q i) (linkedEnum_mem Q j) htwo hZ
      hti htj
  hii := fun i g X hX hcov => hS.mem_normalizer_of_covers hN (linkedEnum_mem Q i) g X hX hcov

theorem linkedClass_eq_singleton (h5 : Theorem5Statement) (hN : NormalInConjNormalizer Q)
    (hND : normalizer (linkedLayer Q : Set G) ≠ ⊤) : linkedClass Q = {Q} := by
  rcases h5 G (linkedLayer Q) _ _ (hS.hyp61 hN) hND with h1 | ⟨h2, hrest⟩
  · obtain ⟨A, hA⟩ := Finset.card_eq_one.mp h1
    have hQ : Q ∈ linkedFinset Q := mem_linkedFinset.mpr (self_mem_linkedClass Q)
    rw [hA, Finset.mem_singleton] at hQ
    ext B
    rw [Set.mem_singleton_iff, ← mem_linkedFinset, hA, Finset.mem_singleton, hQ]
  · exfalso
    have hi : (⟨0, by omega⟩ : Fin (linkedFinset Q).card) ≠ ⟨1, by omega⟩ := by
      simp [Fin.ext_iff]
    obtain ⟨-, hrank, -⟩ := hrest _ _ hi
    have hmem := linkedEnum_mem Q ⟨0, by omega⟩
    rw [preimage_layerBar (twoPrimeLayerIn_le_linkedLayer hmem)] at hrank
    have h4 := ((hS.four_of_mem hmem).mono
      (le_sup_left (b := oddCoreIn (linkedLayer Q)))).two_le_pRank
    omega

theorem not_hasFourGroup_of_linkedClass_eq (hC : linkedClass Q = {Q}) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) :
    ¬ HasFourGroup (rightConjugate Q g ⊓ normalizer (Q : Set G)) := by
  intro h4
  have hle : twoPrimeLayerIn (rightConjugate Q 1) ≤ normalizer (rightConjugate Q g : Set G) := by
    have hI := hS.caseI g 1
    rw [rightConjugate_one] at hI ⊢
    exact hI h4
  have hL := hS.linked_of_le hle
  rw [rightConjugate_one] at hL
  have hmem : rightConjugate Q g ∈ linkedClass Q := ⟨⟨g, rfl⟩, hL⟩
  rw [hC, Set.mem_singleton_iff, rightConjugate_eq_self_iff] at hmem
  exact hg hmem

end MainSetting

end CFSG.ComponentClassification.Asc75T4
