module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G H : Type} [Group G] [Group H] {L : Subgroup G}

theorem ff_cover_pull_E16 [Finite G] {φ : ↥L →* H} (hφ : OddCentralCover φ) {P : Subgroup G}
    (hP : IsSylow2Of P L) {B₁' B₂' : Subgroup H} (hne : B₁' ≠ B₂')
    (h₁ : IsNormalE16In (ffImg φ P) B₁') (h₂ : IsNormalE16In (ffImg φ P) B₂')
    (hcl : ∀ B : Subgroup H, B ≤ ffImg φ P → IsElemAb2 B 4 → B = B₁' ∨ B = B₂') :
    ∃ B₁ B₂ : Subgroup G, B₁ ≠ B₂ ∧ IsNormalE16In P B₁ ∧ IsNormalE16In P B₂ ∧
      ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 → B = B₁ ∨ B = B₂ := by
  have hPL : P ≤ L := hP.1
  have hP2 : IsPGroup 2 P := hP.2.1
  obtain ⟨B₁, hB₁P, hB₁'⟩ := ff_cover_exists_of_le_img hφ hPL hP2 h₁.1
  obtain ⟨B₂, hB₂P, hB₂'⟩ := ff_cover_exists_of_le_img hφ hPL hP2 h₂.1
  have hBne : B₁ ≠ B₂ := by
    intro h
    exact hne (by rw [← hB₁', ← hB₂', h])
  have hn₁' : IsNormalE16In P B₁ := by
    rw [ff_cover_normalE16_iff hφ hPL hP2 hB₁P]
    rwa [hB₁']
  have hn₂' : IsNormalE16In P B₂ := by
    rw [ff_cover_normalE16_iff hφ hPL hP2 hB₂P]
    rwa [hB₂']
  refine ⟨B₁, B₂, hBne, hn₁', hn₂', ?_⟩
  intro B hBP hBe
  have hBL : B ≤ L := le_trans hBP hPL
  have hB2 : IsPGroup 2 B := hP2.to_le hBP
  have hBe' : IsElemAb2 (ffImg φ B) 4 := (ff_cover_elemAb2_iff hφ hBL hB2 4).mp hBe
  rcases hcl (ffImg φ B) (ffImg_mono hBP) hBe' with h | h
  · exact Or.inl (ff_cover_img_injective hφ hPL hP2 hBP hB₁P (by rw [h, hB₁']))
  · exact Or.inr (ff_cover_img_injective hφ hPL hP2 hBP hB₂P (by rw [h, hB₂']))

theorem ff6m_sylow_E16 (G : Type) [Group G] [Finite G] (L : Subgroup G) (h : IsOm6M L)
    (P : Subgroup G) (hP : IsSylow2Of P L) :
    ∃ B₁ B₂ : Subgroup G, B₁ ≠ B₂ ∧ IsNormalE16In P B₁ ∧ IsNormalE16In P B₂ ∧
      ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 → B = B₁ ∨ B = B₂ := by
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff6m_exists_model h
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hφ := ff6m_phi_cover e (ff6m_odd_center h)
  have hPs := ff_cover_isSylow2Of hφ hP
  obtain ⟨B₁', B₂', hne, hn₁, hn₂, hcl, -, -⟩ :=
    ff_star_sylow_E16 hQ hdim hsgn h2 fr hPs
  exact ff_cover_pull_E16 hφ hP hne hn₁ hn₂ hcl

end CFSG.OddStandard.SmallF3.Omega
