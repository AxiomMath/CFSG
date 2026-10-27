module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFieldModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFCoverAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

theorem ff6m_autB_equiv [Finite G] (h : IsOm6M L) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) : Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hB1⟩ := ff_exists_model_B1 h hBL hB
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e (ff6m_odd_center h)
  have hB2 : IsPGroup 2 B := ff_isPGroup_of_isElemAb2 hB
  obtain ⟨e1⟩ := ff_cover_autIn_equiv hφ hBL hB2
  rw [hB1] at e1
  obtain ⟨e2⟩ := ff_star_autIn_equiv hQ hdim hsgn fr
  exact ⟨e1.trans e2⟩

theorem ff6m_autB_trans [Finite G] (h : IsOm6M L) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) :
    ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ n ∈ L ⊓ normalizer (B : Set G), n * b * n⁻¹ = b' := by
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hB1⟩ := ff_exists_model_B1 h hBL hB
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e (ff6m_odd_center h)
  have hB2 : IsPGroup 2 B := ff_isPGroup_of_isElemAb2 hB
  refine ff_cover_trans hφ hBL hB2 ?_
  intro b hb b' hb' hb1 hb1'
  rw [hB1] at hb hb' ⊢
  exact ff_star_trans hQ hdim hsgn fr b hb hb1 b' hb' hb1'

theorem ff6m_autB_cent [Finite G] (h : IsOm6M L) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 4) : L ⊓ centralizer (B : Set G) = B ⊔ centerIn L := by
  obtain ⟨V, _, _, _, Q, hQ, e, fr, hdim, hsgn, hB1⟩ := ff_exists_model_B1 h hBL hB
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e (ff6m_odd_center h)
  refine ff_cover_centralizer_eq hφ hBL hB.1 ?_
  intro n hn
  rw [hB1] at hn ⊢
  exact ff_star_cent_omega hQ hdim hsgn fr n hn

theorem ff6m_aut_B (G : Type) [Group G] [Finite G] (L : Subgroup G) (h : IsOm6M L)
    (P : Subgroup G) (hP : IsSylow2Of P L) (B : Subgroup G) (hBP : B ≤ P) (hB : IsElemAb2 B 4) :
    Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) ∧
      (∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ n ∈ L ⊓ normalizer (B : Set G), n * b * n⁻¹ = b') ∧
      L ⊓ centralizer (B : Set G) = B ⊔ centerIn L :=
  ⟨ff6m_autB_equiv h (hBP.trans hP.1) hB, ff6m_autB_trans h (hBP.trans hP.1) hB,
    ff6m_autB_cent h (hBP.trans hP.1) hB⟩

end CFSG.OddStandard.SmallF3.Omega
