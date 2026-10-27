module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutBasic
public import Certificates.Certificate27203
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Induction.AutBound
open Subgroup

theorem ncard_le_of_rep {L : Array (Array ℕ)} {S : Set PP}
    (h : ∀ z ∈ S, ∃ i < L.size, Rep nn L[i]! z) : S.ncard ≤ L.size := by
  classical
  let f : ℕ → PP := fun i => if hi : ∃ g, Rep nn L[i]! g then hi.choose else 1
  have hsub : S ⊆ f '' ((Finset.range L.size : Finset ℕ) : Set ℕ) := by
    intro z hz
    obtain ⟨i, hi, hrep⟩ := h z hz
    refine ⟨i, by simpa using hi, ?_⟩
    have hex : ∃ g, Rep nn L[i]! g := ⟨z, hrep⟩
    have hfi : f i = hex.choose := by simp [f, hex]
    rw [hfi]
    exact Rep.unique hex.choose_spec hrep
  calc S.ncard ≤ (f '' ((Finset.range L.size : Finset ℕ) : Set ℕ)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((Finset.range L.size : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_image_le (Finset.finite_toSet _)
    _ = L.size := by rw [Set.ncard_coe_finset, Finset.card_range]

section Classes

theorem closure_gGen2 (σ : PP) : Subgroup.closure (gGen σ '' {j | j < 2}) = twoBD := by
  have : gGen σ '' {j | j < 2} = {xBar, yBar} := by
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j <;> simp [gGen]
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp [gGen]⟩
      · exact ⟨1, by norm_num, by simp [gGen]⟩
  rw [this]

theorem g24_classes :
    ∃ tA : PP, Rep nn tAa tA ∧ tA ∈ twoBD ∧ tA * tA = 1 ∧ tA ≠ 1 ∧
      (∀ i < laList.size, ∃ d ∈ twoBD, Rep nn laList[i]! (d * tA * d⁻¹)) ∧
      (∀ z, (∃ d ∈ twoBD, z = d * tA * d⁻¹) → ∃ i < laList.size, Rep nn laList[i]! z) ∧
      laList.size = 4095 ∧ 4096 ≤ {z : PP | ∃ d ∈ twoBD, z = d * xBar * d⁻¹}.ncard ∧
      ∀ z ∈ twoBD, z * z = 1 → z ≠ 1 →
        (∃ d ∈ twoBD, d * z * d⁻¹ = tA) ∨ ∃ d ∈ twoBD, d * z * d⁻¹ = xBar := by
  have h := Certificates.certificate27203
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY] at h
  obtain ⟨tA, htA, htAD, hsq, hne, hgen, hcl, hsz, hlb, hfus, -⟩ := h
  exact ⟨tA, htA, htAD, hsq, hne, hgen, hcl, hsz, hlb, hfus⟩

end Classes

end CFSG.EvenSporadicStandard.G24Aut
