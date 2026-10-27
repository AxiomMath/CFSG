module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Extra
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Inf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGz_three (hC : CSideFacts) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hIrr : CIrreducible ↥(Gx z) (CFSG.pCore 2 ↥(Gx z))) :
    (∀ σ : ↥(Gx z), orderOf σ = 3 →
        (IsShapeZpTimesA5 3 ↥(CbarCent z σ) ∧ Qz z ⊓ Gx (σ : G) = Subgroup.zpowers z) ∨
        (IsShapeZpWrTwo 3 ↥(CbarCent z σ) ∧ IsPlusExtraspecial 2 (Qz z ⊓ Gx (σ : G)))) ∧
      (∃ σ : ↥(Gx z), orderOf σ = 3 ∧ IsShapeZpTimesA5 3 ↥(CbarCent z σ)) ∧
      (∃ σ : ↥(Gx z), orderOf σ = 3 ∧ IsShapeZpWrTwo 3 ↥(CbarCent z σ)) := by
  have hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  obtain ⟨h1, h2, h3⟩ := hC.three_local ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) hQ hIrr
  refine ⟨fun σ hσ => ?_, h2, h3⟩
  rcases h1 σ hσ with ⟨hs, hq⟩ | ⟨hs, hq⟩
  · exact Or.inl ⟨hs, (structGz_qzInf_eq_zpowers_iff h σ).mp hq⟩
  · refine Or.inr ⟨hs, ?_⟩
    rw [structGz_qzInf_eq_map z σ]
    exact structGz_isPlusExtraspecial_map (Gx z).subtype_injective hq

end CFSG.EvenSporadicStandard.HNRecog.Section3
