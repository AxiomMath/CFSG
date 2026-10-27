module

public import CFSG.ClassicalInvolution.Q3.Q3LLie

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification
open scoped commutatorElement

theorem le_sup_centralizer_of_lieSystemMod3 (hM : M11Facts) {G : Type} [Group G] [Finite G]
    {Λ : Set (Subgroup G)} (hLie : LieSystemMod3 Λ) {L : Subgroup G} (hL : L ∈ Λ)
    {T : Subgroup G} (hT : IsComponentOf T ⊤) (hTO : T ⊓ classicalInvolutionOddCore G = ⊥) :
    L ≤ T ⊔ Subgroup.centralizer (T : Set G) := by
  obtain ⟨ι, hι, ⟨D⟩⟩ := hLie
  set O : Subgroup G := classicalInvolutionOddCore G with hOdef
  set π : G →* G ⧸ O := QuotientGroup.mk' O with hπ
  have hTbot : T ≠ ⊥ := by
    intro h
    have : Nontrivial T := Quasisimple.nontrivial hT.2.2
    exact (Subgroup.nontrivial_iff_ne_bot T).mp this h
  have hTnk : ¬ T ≤ π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    intro h
    exact hTbot (eq_bot_iff.mpr (hTO ▸ le_inf le_rfl h))
  have hTbar : IsComponentOf (T.map π) ⊤ :=
    LocalComponents.image hT π (QuotientGroup.mk'_surjective O) hTnk
  obtain ⟨i, R, -, hRL⟩ := D.fundamental (L.map π) ⟨L, hL, rfl⟩
  have hLle : L.map π ≤ (D.hom i).range := by
    rw [hRL]
    exact Subgroup.map_le_range _ _
  have hOT : ⁅T, O⁆ = ⊥ := by
    rcases LocalComponents.normal_contains_or_commutes T O hT with h | h
    · exact absurd (eq_bot_iff.mpr (hTO ▸ le_inf le_rfl h)) hTbot
    · exact h
  have hOc : O ≤ Subgroup.centralizer (T : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 : ⁅t, o⁆ ∈ ⁅T, O⁆ := Subgroup.commutator_mem_commutator ht ho
    rw [hOT, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
  rcases LieSystemData3.component_dichotomy hM D hTbar i hLle with h | h
  · have h1 : L ≤ Subgroup.comap π (T.map π) := Subgroup.map_le_iff_le_comap.mp h
    rw [Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk'] at h1
    exact h1.trans (sup_le_sup_left hOc _)
  · have hLT : ⁅L, T⁆ ≤ O := by
      have h2 : (⁅L, T⁆).map π = ⊥ := by rw [Subgroup.map_commutator]; exact h
      have h3 := (Subgroup.map_eq_bot_iff _).mp h2
      rwa [hπ, QuotientGroup.ker_mk'] at h3
    have hperf : Group.IsPerfect T := ⟨hT.2.2.1⟩
    have hdouble : ⁅⁅T, L⁆, T⁆ = ⊥ := by
      rw [Subgroup.commutator_comm T L]
      refine le_bot_iff.mp ?_
      calc ⁅⁅L, T⁆, T⁆ ≤ ⁅O, T⁆ := Subgroup.commutator_mono hLT le_rfl
        _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hOT
        _ ≤ ⊥ := le_rfl
    have hTL : ⁅T, L⁆ = ⊥ := Quasisimple.perfect_double_commutator T L hdouble
    refine le_sup_of_le_right ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hTL

end CFSG.ClassicalInvolution.Q3
