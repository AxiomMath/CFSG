module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Extra
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Inf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGz_five (hC : CSideFacts) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hA : AschbacherHyp ↥(Gx z) (CFSG.pCore 2 ↥(Gx z))) :
    (∀ ρ : ↥(Gx z), orderOf ρ = 5 →
        (IsShapeZpTimesA5 5 ↥(CbarCent z ρ) ∧ Qz z ⊓ Gx (ρ : G) = Subgroup.zpowers z) ∨
        (IsShapeZpTimesZp 5 ↥(CbarCent z ρ) ∧ IsMinusExtraspecial 2 (Qz z ⊓ Gx (ρ : G))) ∨
        (IsShapeZpWrTwo 5 ↥(CbarCent z ρ) ∧ Qz z ⊓ Gx (ρ : G) = Subgroup.zpowers z)) ∧
      (∃ ρ : ↥(Gx z), orderOf ρ = 5 ∧ IsShapeZpTimesA5 5 ↥(CbarCent z ρ)) ∧
      (∃ ρ : ↥(Gx z), orderOf ρ = 5 ∧ IsShapeZpTimesZp 5 ↥(CbarCent z ρ)) ∧
      (∃ ρ : ↥(Gx z), orderOf ρ = 5 ∧ IsShapeZpWrTwo 5 ↥(CbarCent z ρ)) := by
  have hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  obtain ⟨-, h2, h3, h4⟩ :=
    hC.five_local_shapes ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) hQ hA.irreducible
  refine ⟨fun ρ hρ => ?_, h2, h3, h4⟩
  rcases hC.five_local ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) hA ρ hρ with
    ⟨hs, hq⟩ | ⟨hs, hq⟩ | ⟨hs, hq⟩
  · exact Or.inl ⟨hs, (structGz_qzInf_eq_zpowers_iff h ρ).mp hq⟩
  · refine Or.inr (Or.inl ⟨hs, ?_⟩)
    rw [structGz_qzInf_eq_map z ρ]
    exact structGz_isMinusExtraspecial_map (Gx z).subtype_injective hq
  · exact Or.inr (Or.inr ⟨hs, (structGz_qzInf_eq_zpowers_iff h ρ).mp hq⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section3
