module

public import CFSG.ClassicalInvolution.Asc77.AscT7U4
public import CFSG.ClassicalInvolution.Asc77.AscT7U7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7U

section Residual

variable (p f : ℕ) [Fact p.Prime]


@[expose] def C25_16inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 → ¬ IsFAut R' a

end Residual

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem c25_12_of_11 (h11 : C25_11 p f) : C25_12 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have haN : a ∈ Subgroup.normalizer (R : Set G) := hF.1
  have hVle : R ⊔ Subgroup.zpowers a ≤ (S : Subgroup G) :=
    sup_le h.hRS (Subgroup.zpowers_le.mpr haS)
  have hV2 : IsPGroup 2 ↥(R ⊔ Subgroup.zpowers a) := S.isPGroup'.to_le hVle
  have hVn : R ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr haN)
  have hVR : ∀ y ∈ R ⊔ Subgroup.zpowers a, conjSub y R = R := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mp (hVn hy)
  have haz : a * a ∈ Subgroup.zpowers z := by
    have := h11 G Ω K K' W S R R' z t u₁ u₂ hyp
    rw [← this]
    exact ⟨Subgroup.mul_mem _ haS haS, ha2⟩
  obtain ⟨r, hr, hb2, hbF⟩ := exists_involution_of_isFAut h.hqR h.hzR le_sup_left hV2 hVR
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) hF haz
  exact ⟨a * r, ⟨r, hr, rfl⟩, hb2, hbF⟩

theorem c25_16sq_of_inv (hres : C25_16inv p f) : C25_16sq p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have haN : a ∈ Subgroup.normalizer (R' : Set G) := hF.1
  have hVle : R' ⊔ Subgroup.zpowers a ≤ (S : Subgroup G) :=
    sup_le h.hR'S (Subgroup.zpowers_le.mpr haS)
  have hV2 : IsPGroup 2 ↥(R' ⊔ Subgroup.zpowers a) := S.isPGroup'.to_le hVle
  have hVn : R' ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (R' : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr haN)
  have hVR : ∀ y ∈ R' ⊔ Subgroup.zpowers a, conjSub y R' = R' := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mp (hVn hy)
  have hza : a * a ∈ Subgroup.zpowers z := ha2
  obtain ⟨r, hr, hb2, hbF⟩ := exists_involution_of_isFAut h.hqR' h.hzR' le_sup_left hV2 hVR
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) hF hza
  exact hres G Ω K K' W S R R' z t u₁ u₂ hyp (a * r)
    (Subgroup.mul_mem _ haS (h.hR'S hr)) hb2 hbF

theorem c25_16_of_inv (h11 : C25_11 p f) (hres : C25_16inv p f) : C25_16 p f :=
  c25_16_of_sq h11 (c25_16sq_of_inv hres)

theorem c25_16inv_of_16 (h : C25_16 p f) : C25_16inv p f :=
  fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS _ => h G Ω K K' W S R R' z t u₁ u₂ hyp a haS

theorem c25_16sq_of_16 (h : C25_16 p f) : C25_16sq p f :=
  fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS _ => h G Ω K K' W S R R' z t u₁ u₂ hyp a haS

theorem c25_16_iff_inv (h11 : C25_11 p f) : C25_16 p f ↔ C25_16inv p f :=
  ⟨c25_16inv_of_16, c25_16_of_inv h11⟩

end Main

end T7U

end CFSG.ClassicalInvolution.Asc77
