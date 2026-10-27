module

public import CFSG.ClassicalInvolution.Asc77.AscT8YB2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T8YY

section NoFinite

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K J W : Subgroup G} {z t : G}

theorem omegaNbr_ncard_conjE (hΩ : ConjInvariant Ω) (K : Subgroup G) (g : G) :
    (omegaNbr Ω (conjSub g K)).ncard = (omegaNbr Ω K).ncard := by
  have h1 : omegaNbr Ω (conjSub g K) = conjSub g '' omegaNbr Ω K := by
    ext L
    constructor
    · intro hL
      refine ⟨conjSub g⁻¹ L, ?_, conjSub_conjSub_inv g L⟩
      have := omegaNbr_conj hΩ hL g⁻¹
      rwa [conjSub_inv_conjSub] at this
    · rintro ⟨J, hJ, rfl⟩
      exact omegaNbr_conj hΩ hJ g
  rw [h1, Set.ncard_image_of_injective _ (conjSub_injective g)]

namespace FrameData

@[expose] def othersE (F : FrameData Ω W K J z t) (i : Fin 4) : Set (Subgroup G) :=
  {L | ∃ j, j ≠ i ∧ L = (F.ρ j).K}

theorem ncard_othersE (F : FrameData Ω W K J z t) (i : Fin 4) : (F.othersE i).ncard = 3 := by
  classical
  have hinj : Function.Injective (fun j : Fin 4 => (F.ρ j).K) := by
    intro j j' hjj'
    by_contra hne
    exact F.hne j j' hne hjj'
  have h : F.othersE i = (fun j : Fin 4 => (F.ρ j).K) '' {j : Fin 4 | j ≠ i} := by
    ext L
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
  have h3 : {j : Fin 4 | j ≠ i} = ((Finset.univ.erase i : Finset (Fin 4)) : Set (Fin 4)) := by
    ext j
    simp
  rw [h, Set.ncard_image_of_injective _ hinj, h3, Set.ncard_coe_finset,
    Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

end FrameData

end NoFinite

section WithFinite

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J W : Subgroup G} {z t : G}

theorem neighbours_of_frame_of_zero_of (hΩ : ConjInvariant Ω) (hK : K ∈ Ω)
    (htrans : ∀ L ∈ Ω, ∃ g : G, conjSub g K = L) (F : FrameData Ω W K J z t)
    (h0 : ∀ M ∈ omegaNbr Ω K, ∃ j, M = (F.ρ j).K) :
    ∀ i : Fin 4, ∀ M ∈ omegaNbr Ω (F.ρ i).K, ∃ j, M = (F.ρ j).K := by
  have hK3 : (omegaNbr Ω K).ncard = 3 := by
    have : omegaNbr Ω K = F.othersE 0 := by
      ext M
      constructor
      · intro hM
        obtain ⟨j, rfl⟩ := h0 M hM
        refine ⟨j, fun hj => ?_, rfl⟩
        apply hM.2.1
        rw [hj, F.h0]
      · rintro ⟨j, hj, rfl⟩
        have := F.hadj 0 j (Ne.symm hj)
        rwa [F.h0] at this
    rw [this, F.ncard_othersE]
  intro i M hM
  have hLΩ : (F.ρ i).K ∈ Ω := (F.ρ i).hK
  obtain ⟨g, hg⟩ := htrans (F.ρ i).K hLΩ
  have hcard : (omegaNbr Ω (F.ρ i).K).ncard = 3 := by
    rw [← hg, omegaNbr_ncard_conjE hΩ K g, hK3]
  have hsub : F.othersE i ⊆ omegaNbr Ω (F.ρ i).K := by
    rintro _ ⟨j, hj, rfl⟩
    exact F.hadj i j (Ne.symm hj)
  have heq : F.othersE i = omegaNbr Ω (F.ρ i).K :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, F.ncard_othersE]) (Set.toFinite _)
  rw [← heq] at hM
  obtain ⟨j, -, rfl⟩ := hM
  exact ⟨j, rfl⟩

end WithFinite

end T8YY

end CFSG.ClassicalInvolution.Asc77
