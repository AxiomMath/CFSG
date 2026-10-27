module

public import CFSG.ClassicalInvolution.Asc77.AscT8YB2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)
open scoped commutatorElement

namespace T8ZZ

variable {G : Type} [Group G] [Finite G]

theorem commute_of_normalizes_sylowE {L P : Subgroup G} (hP : IsPGroup 2 P) (hPL : P ≤ L) {a : G}
    (haP : conjSub a P = P) (hcomm : ∀ k ∈ L, ⁅a, k⁆ ∈ oddCoreOf L) {r : G} (hr : r ∈ P) :
    r * a = a * r := by
  have h1 : a * r * a⁻¹ ∈ P := haP ▸ conj_mem_conjSub hr
  have h2 : ⁅a, r⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem h1 (P.inv_mem hr)
  have h3 : ⁅a, r⁆ ∈ oddCoreOf L := hcomm r (hPL hr)
  have h4 : ⁅a, r⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) h3
      (hP.to_le (Subgroup.zpowers_le.mpr h2))
  rw [commutatorElement_def] at h4
  calc r * a = (a * r * a⁻¹ * r⁻¹) * (r * a) := by rw [h4, one_mul]
    _ = a * r := by group

variable {Ω : Set (Subgroup G)} {K J W : Subgroup G} {z t : G}

theorem commonNbr_frame_eq_of (F : FrameData Ω W K J z t) {j : Fin 4} (hj : j ≠ 0)
    {L : Subgroup G} (hLK : L ∈ omegaNbr Ω K) (hLj : L ∈ omegaNbr Ω (F.ρ j).K)
    (hnc2 : ∀ {M : Subgroup G}, M ∈ omegaNbr Ω K → (omegaNbr Ω K ∩ omegaNbr Ω M).ncard ≤ 2) :
    ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ L = (F.ρ i).K := by
  have hjK : (F.ρ j).K ∈ omegaNbr Ω K := by
    have := F.hadj 0 j (Ne.symm hj)
    rwa [F.h0] at this
  have hcard := hnc2 hjK
  let E : Set (Subgroup G) := {L | ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ L = (F.ρ i).K}
  have hEsub : E ⊆ omegaNbr Ω K ∩ omegaNbr Ω (F.ρ j).K := by
    rintro _ ⟨i, hi0, hij, rfl⟩
    refine ⟨?_, F.hadj j i (Ne.symm hij)⟩
    have := F.hadj 0 i (Ne.symm hi0)
    rwa [F.h0] at this
  have hinj : Function.Injective (fun i : Fin 4 => (F.ρ i).K) := by
    intro a b hab
    by_contra hne'
    exact F.hne a b hne' hab
  have hEcard : E.ncard = 2 := by
    have h1 : E = (fun i : Fin 4 => (F.ρ i).K) '' {i : Fin 4 | i ≠ 0 ∧ i ≠ j} := by
      ext L
      constructor
      · rintro ⟨i, hi0, hij, rfl⟩
        exact ⟨i, ⟨hi0, hij⟩, rfl⟩
      · rintro ⟨i, ⟨hi0, hij⟩, rfl⟩
        exact ⟨i, hi0, hij, rfl⟩
    have h2 : {i : Fin 4 | i ≠ 0 ∧ i ≠ j} =
        (((Finset.univ.erase 0).erase j : Finset (Fin 4)) : Set (Fin 4)) := by
      ext i
      simp [and_comm]
    rw [h1, Set.ncard_image_of_injective _ hinj, h2, Set.ncard_coe_finset,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp
  have heq : E = omegaNbr Ω K ∩ omegaNbr Ω (F.ρ j).K :=
    Set.eq_of_subset_of_ncard_le hEsub (by rw [hEcard]; exact hcard) (Set.toFinite _)
  have hL : L ∈ E := by
    rw [heq]
    exact ⟨hLK, hLj⟩
  exact hL

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
