module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22FusionData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KInvolutions
public import Certificates.Certificate24783

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std (FixedData)

theorem fixedCheck_spec :
    (stabTabs.length = 2 ∧ ∀ g ∈ stabTabs, normOK (elemTabs 1) g = true ∧
      TabCheck.comm g tTab = true) ∧
    (∀ x ∈ elemTabs 1, (∀ g ∈ stabTabs, tmul g x = tmul x g ∨
      tmul g x = tmul (tmul x tTab) g) → x = tTab) := by
  have h := Certificates.certificate24783
  simp only [fixedCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem exists_elt_of_mem_stabTabs {g : Tab} (hg : g ∈ stabTabs) :
    ∃ s : Carrier .M22, tab s = g := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact ⟨wordElt [genA, genB, genBi] w, by rw [tab_wordElt, tab_letters]⟩

theorem fixedData_pinned
    {F1 : Subgroup (Carrier .M22)} (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    FixedData (⊤ : Subgroup (Carrier .M22)) F1 := by
  obtain ⟨hstab, hFP⟩ := fixedCheck_spec
  refine ⟨fun f hf hf1 x hx H => ?_⟩
  have hfm : f ∈ invs16 1 := ((hmem1 f).1 hf).resolve_left hf1
  obtain ⟨b, hbn, hbt⟩ := exists_conj_tEl hmem1 f hfm
  have hbmem : b ∈ Subgroup.normalizer (F1 : Set (Carrier .M22)) :=
    Subgroup.mem_normalizer_iff.2 hbn
  have hbinv := Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbmem)
  have hx'F : b⁻¹ * x * b⁻¹⁻¹ ∈ F1 := (hbinv x).1 hx
  rw [inv_inv] at hx'F
  by_cases hx'1 : b⁻¹ * x * b = 1
  · left
    have : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    rw [this, hx'1]
    group
  · right
    obtain ⟨x', hx'⟩ : ∃ x', x' = b⁻¹ * x * b := ⟨_, rfl⟩
    have hx'F' : x' ∈ F1 := hx' ▸ hx'F
    have hx'1' : x' ≠ 1 := hx' ▸ hx'1
    have hx'm : x' ∈ invs16 1 := ((hmem1 _).1 hx'F').resolve_left hx'1'
    have hxt : tab x' ∈ elemTabs 1 := by
      rw [← tab_invs16]
      exact List.mem_map_of_mem hx'm
    have hx't : x' = tEl := by
      apply tab_injective
      rw [tab_tEl]
      refine hFP _ hxt (fun g hg => ?_)
      obtain ⟨s, hs⟩ := exists_elt_of_mem_stabTabs hg
      obtain ⟨hsn, hsc⟩ := hstab.2 g hg
      have hsmem : s ∈ Subgroup.normalizer (F1 : Set (Carrier .M22)) :=
        Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 (by rw [hs]; exact hsn))
      have hst : s * tEl = tEl * s :=
        tab_injective (by rw [tab_mul, tab_mul, tab_tEl, hs]; exact of_decide_eq_true hsc)
      have hn' : b * s * b⁻¹ ∈ Subgroup.normalizer (F1 : Set (Carrier .M22)) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hbmem hsmem) (Subgroup.inv_mem _ hbmem)
      have hb'f : (b * s * b⁻¹) * f * (b * s * b⁻¹)⁻¹ = f := by
        rw [← hbt]
        calc b * s * b⁻¹ * (b * tEl * b⁻¹) * (b * s * b⁻¹)⁻¹ = b * (s * tEl * s⁻¹) * b⁻¹ := by
              group
          _ = b * tEl * b⁻¹ := by rw [hst]; group
      have hH := H (b * s * b⁻¹) (Subgroup.mem_top _) (Subgroup.mem_normalizer_iff.1 hn') hb'f
      have hconj : b * s * b⁻¹ * x * (b * s * b⁻¹)⁻¹ = b * (s * x' * s⁻¹) * b⁻¹ := by
        rw [hx']
        group
      have hbx : x = b * x' * b⁻¹ := by
        rw [hx']
        group
      have hbf : x * f = b * (x' * tEl) * b⁻¹ := by
        rw [hx', ← hbt]
        group
      rcases hH with h1 | h1
      · left
        rw [hconj] at h1
        have h3 : b * (s * x' * s⁻¹) * b⁻¹ = b * x' * b⁻¹ := by rw [h1]; exact hbx
        have h2 : s * x' * s⁻¹ = x' := mul_left_cancel (mul_right_cancel h3)
        have h4 : s * x' = x' * s := mul_inv_eq_iff_eq_mul.1 h2
        have := congrArg tab h4
        rw [tab_mul, tab_mul, hs] at this
        exact this
      · right
        rw [hconj, hbf] at h1
        have h2 : s * x' * s⁻¹ = x' * tEl := mul_left_cancel (mul_right_cancel h1)
        have h4 : s * x' = x' * tEl * s := mul_inv_eq_iff_eq_mul.1 h2
        have := congrArg tab h4
        rw [tab_mul, tab_mul, tab_mul, hs, tab_tEl] at this
        exact this
    have hxe : x = b * x' * b⁻¹ := by
      rw [hx']
      group
    rw [hxe, hx't, hbt]

end CFSG.EvenSporadicStandard.M22Std
