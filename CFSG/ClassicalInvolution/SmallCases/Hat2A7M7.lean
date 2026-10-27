module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M7
public import CFSG.ClassicalInvolution.Asc77.AscT7U7
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Hat2A7M
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
in
theorem exists_hyp25T (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    ∃ t' : G, T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t' := by
  obtain ⟨t', hT⟩ := CFSG.ClassicalInvolution.T7F25.Asc77.T7T.exists_hyp25T hyp.toF
  exact ⟨t', hyp, hT.ht'S, hT.ht'2, hT.ht'R⟩
end T7T
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7U
open CFSG.ClassicalInvolution.Asc77.T7U
section Residual
@[expose] def C25_16sqR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a ∈ R → ¬ IsFAut R' a
end Residual
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
theorem sq_mem_of_isFAut (h : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (h11 : C25_11) (hres : C25_16sqR) {a : G} (haS : a ∈ (S : Subgroup G))
    (hF : IsFAut R' a) : a * a ∈ R :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7U.sq_mem_of_isFAut h.toF
    (h11 G Ω K K' W S R R' z t u₁ u₂ h.hyp) (hres G Ω K K' W S R R' z t u₁ u₂ h.hyp) haS hF
theorem c25_16_of_sqR (h11 : C25_11) (hres : C25_16sqR) : C25_16 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS hF
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  exact hres G Ω K K' W S R R' z t u₁ u₂ hyp a haS (sq_mem_of_isFAut h h11 hres haS hF) hF
end Main
end T7U
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7U
open CFSG.ClassicalInvolution.Asc77.T7U
section Residual
@[expose] def C25_16sq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G),
      a * a ∈ Subgroup.zpowers z → ¬ IsFAut R' a
end Residual
section Main
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
theorem exists_sq_mem_zpowers_of_isFAut (h : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    {a : G} (haS : a ∈ (S : Subgroup G)) (hF : IsFAut R' a) (haR : a * a ∈ R) :
    ∃ a₁ ∈ (S : Subgroup G), a₁ * a₁ ∈ Subgroup.zpowers z ∧ IsFAut R' a₁ :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7U.exists_sq_mem_zpowers_of_isFAut h.toF haS hF haR
theorem c25_16sqR_of_sq (hres : C25_16sq) : C25_16sqR := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS haR hF
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  obtain ⟨a₁, ha₁S, ha₁sq, ha₁F⟩ := exists_sq_mem_zpowers_of_isFAut h haS hF haR
  exact hres G Ω K K' W S R R' z t u₁ u₂ hyp a₁ ha₁S ha₁sq ha₁F
theorem c25_16_of_sq (h11 : C25_11) (hres : C25_16sq) : C25_16 :=
  c25_16_of_sqR h11 (c25_16sqR_of_sq hres)
end Main
end T7U
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
namespace T7U
open CFSG.ClassicalInvolution.Asc77.T7U
section Residual
@[expose] def C25_16inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 → ¬ IsFAut R' a
end Residual
section Main
theorem c25_16sq_of_inv (hres : C25_16inv) : C25_16sq := by
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
theorem c25_16_of_inv (h11 : C25_11) (hres : C25_16inv) : C25_16 :=
  c25_16_of_sq h11 (c25_16sq_of_inv hres)
end Main
end T7U
end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7M
