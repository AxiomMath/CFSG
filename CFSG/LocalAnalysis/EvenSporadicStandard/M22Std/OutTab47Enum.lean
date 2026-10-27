module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsExtra2
public import Certificates.Certificate24790

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.FusionCheck CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.M23Std

abbrev autNorm (F : Subgroup (Carrier .M22)) : Subgroup (MulAut (Carrier .M22)) :=
  normalizer ((innerImage (Carrier .M22) F : Subgroup (MulAut (Carrier .M22))) :
    Set (MulAut (Carrier .M22)))

@[expose] def tabMapY : TabMap (Carrier .M22) :=
  ⟨tab, tab_mul, tab_one, tab_injective⟩

@[expose] def nGensElt : List (Carrier .M22) := nGensWords.map (wordElt [genA, genB, genBi])

theorem tab_wordElt_letters (w : List Nat) :
    tab (wordElt [genA, genB, genBi] w) = wordTab letterTabs w := by
  rw [tab_wordElt, tab_letters]

theorem map_tab_nGensElt : nGensElt.map tab = nGensTab := by
  simp only [nGensElt, nGensTab, List.map_map]
  exact List.map_congr_left fun w _ => tab_wordElt_letters w

theorem tab_wordElt_nGens (w : List Nat) : tab (wordElt nGensElt w) = wordTab nGensTab w := by
  rw [tab_wordElt, map_tab_nGensElt]

section Words

variable {F1 : Subgroup (Carrier .M22)} (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
  (hnorm : ∀ g ∈ nGensTab, normOK (elemTabs 1) g = true)
include hmem1 hnorm

theorem nGensElt_mem : ∀ g ∈ nGensElt, g ∈ normalizer (F1 : Set (Carrier .M22)) := by
  intro g hg
  have h : normOK (elemTabs 1) (tab g) = true :=
    hnorm _ (by rw [← map_tab_nGensElt]; exact List.mem_map_of_mem hg)
  exact Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 h)

theorem wordElt_nGens_mem (w : List Nat) :
    wordElt nGensElt w ∈ normalizer (F1 : Set (Carrier .M22)) :=
  wordElt_mem fun j _ => getD_mem (nGensElt_mem hmem1 hnorm) j

theorem exists_of_mem_tabLI {l : Tab} (hl : l ∈ tabLI) :
    ∃ y ∈ normalizer (F1 : Set (Carrier .M22)), tab y = l := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 (show l ∈ innerWords.map (wordTab nGensTab) from hl)
  exact ⟨wordElt nGensElt w, wordElt_nGens_mem hmem1 hnorm w, tab_wordElt_nGens w⟩

end Words

section Enum


variable {F1 : Subgroup (Carrier .M22)}

theorem card_innerImage_top_inf (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (D : NData (⊤ : Subgroup (Carrier .M22)) F1) :
    Nat.card ↥(innerImage (Carrier .M22) ⊤ ⊓ autNorm F1) = 5760 := by
  have hNI : innerImage (Carrier .M22) ⊤ ⊓ autNorm F1 =
      (normalizer (F1 : Set (Carrier .M22))).map MulAut.conj := by
    ext α
    constructor
    · rintro ⟨⟨y, -, rfl⟩, hα⟩
      refine ⟨y, ?_, rfl⟩
      show y ∈ normalizer (F1 : Set (Carrier .M22))
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have := (mem_normalizer_innerImage_iff conj_injective_m22).1 hα x
      simpa [MulAut.conj_apply] using this
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_top _, rfl⟩, conj_mem_normalizer hy⟩
  rw [hNI, Subgroup.card_map_of_injective conj_injective_m22, card_normalizer_F1 hF D]


theorem isTabsOf_inner (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (D : NData (⊤ : Subgroup (Carrier .M22)) F1) :
    autTabMap.IsTabsOf (innerImage (Carrier .M22) ⊤ ⊓ autNorm F1) tabLI := by
  obtain ⟨hnorm, ⟨hlen, hnd⟩, -⟩ := censusCheck_spec Certificates.certificate24790
  have hcard := card_innerImage_top_inf hF D
  have : Finite ↥(innerImage (Carrier .M22) ⊤ ⊓ autNorm F1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine TabMap.isTabsOf_of_exists autTabMap _ tabLI (fun l hl => ?_) hnd (by rw [hlen, hcard])
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_tabLI hF hnorm hl
  exact ⟨MulAut.conj y, ⟨⟨y, Subgroup.mem_top _, rfl⟩, conj_mem_normalizer hy⟩, autTab_conj y⟩

theorem isTabsOf_N (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (D : NData (⊤ : Subgroup (Carrier .M22)) F1) : autTabMap.IsTabsOf (autNorm F1) tabL := by
  obtain ⟨hnorm, -, ⟨hlen, hnd⟩, -⟩ := censusCheck_spec Certificates.certificate24790
  have hcard := card_normalizer_innerImage hF D
  have : Finite ↥(autNorm F1) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine TabMap.isTabsOf_of_exists autTabMap _ tabL (fun l hl => ?_) hnd (by rw [hlen, hcard])
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨y, hy, rfl⟩ := exists_of_mem_tabLI hF hnorm hl
    exact ⟨MulAut.conj y, conj_mem_normalizer hy, autTab_conj y⟩
  · obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_tabLI hF hnorm hl0
    refine ⟨betaAut * MulAut.conj y, Subgroup.mul_mem _ (betaAut_mem_normalizer hF)
      (conj_mem_normalizer hy), ?_⟩
    show autTab (betaAut * MulAut.conj y) = tmul betaTab (tab y)
    rw [autTab_mul, autTab_betaAut, autTab_conj]

end Enum

section F1Tabs

variable {F1 : Subgroup (Carrier .M22)}

theorem isTabsOf_F1 (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) : tabMapY.IsTabsOf F1 f1Tabs := by
  refine ⟨fun x hx => ?_, fun l hl => ?_⟩
  · rcases (hF x).1 hx with rfl | hx
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (by rw [← tab_invs16]; exact List.mem_map_of_mem hx)
  · rcases List.mem_cons.1 hl with rfl | hl
    · exact ⟨1, F1.one_mem, tab_one⟩
    · rw [← tab_invs16] at hl
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
      exact ⟨y, (hF y).2 (Or.inr hy), rfl⟩


theorem isTabsOf_innerImage (hF : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    autTabMap.IsTabsOf (innerImage (Carrier .M22) F1) f1Tabs := by
  have h := isTabsOf_F1 hF
  refine ⟨fun α hα => ?_, fun l hl => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hα
    show autTab (MulAut.conj x) ∈ f1Tabs
    rw [autTab_conj]
    exact h.mem x hx
  · obtain ⟨y, hy, rfl⟩ := h.exists_mem l hl
    exact ⟨MulAut.conj y, ⟨y, hy, rfl⟩, autTab_conj y⟩

end F1Tabs

end CFSG.EvenSporadicStandard.M22Std
