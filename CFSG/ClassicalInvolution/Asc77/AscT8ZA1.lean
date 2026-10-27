module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleClique

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD.Exotic (span_le_perp_of_negSpace)

namespace T8ZZ

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem La_neg_one_mul_eq_neg_of_orth (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V = 8)
    {F₁ F₂ : Frame Q}
    (h : ∀ x ∈ negSpace (F₁.La (-1)), ∀ y ∈ negSpace (F₂.La (-1)), polar Q x y = 0) (v : V) :
    (F₁.La (-1) * F₂.La (-1)) v = (-1 : K) • v := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have h12 : F₂.span ≤ F₁.perp := span_le_perp_of_negSpace hodd h
  have h21 : F₁.span ≤ F₂.perp :=
    span_le_perp_of_negSpace hodd (fun x hx y hy => by rw [polar_comm]; exact h y hy x hx)
  have d1 : Module.finrank K F₁.perp = 4 := by
    have := ModelFacts.finrank_perp_add_four F₁
    omega
  have e12 : F₂.span = F₁.perp :=
    Submodule.eq_of_le_of_finrank_eq h12 (by rw [Frame.finrank_span, d1])
  have hv : v ∈ F₁.span ⊔ F₁.perp := by
    rw [(Frame.isCompl_span_perp F₁).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hb2 : b ∈ F₂.span := by rw [e12]; exact hb
  have a1 : F₁.La (-1) a = -a := (Frame.mem_span_iff_inv F₁ h2).mp ha
  have b1 : F₁.La (-1) b = b := (Frame.mem_perp_iff_fix F₁ h2).mp hb
  have a2 : F₂.La (-1) a = a := (Frame.mem_perp_iff_fix F₂ h2).mp (h21 ha)
  have b2 : F₂.La (-1) b = -b := (Frame.mem_span_iff_inv F₂ h2).mp hb2
  rw [LinearEquiv.mul_apply, map_add, a2, b2, map_add, map_neg, a1, b1]
  simp only [neg_smul, one_smul, neg_add_rev]
  abel

theorem fund_prod_scalar (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V = 8)
    {L₁ L₂ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ : V ≃ₗ[K] V} (h₁ : IsFundamental Q L₁ i₁)
    (h₂ : IsFundamental Q L₂ i₂) (hc : Commutes L₁ L₂) :
    ∃ c : K, ∀ v, (i₁ * i₂) v = c • v := by
  rcases CFSG.ClassicalInvolution.RouteD.Gaps.orth_or_twin hodd h₁ h₂ hc with horth | heq
  · obtain ⟨F₁, rfl, rfl⟩ := h₁
    obtain ⟨F₂, rfl, rfl⟩ := h₂
    exact ⟨-1, La_neg_one_mul_eq_neg_of_orth hodd hdim horth⟩
  · subst heq
    refine ⟨1, fun v => ?_⟩
    rw [h₁.mul_self]
    simp

end Geometry

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
