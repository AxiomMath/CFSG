module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadFrame
public import CFSG.ClassicalInvolution.Q3.Q3T8B04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform

section Std


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.BadStd8.eq_conjClass
    (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t) : Ω = CoreAssembly.conjClass K := by
  ext M
  constructor
  · intro hM
    obtain ⟨g, hg⟩ := h.std.stand.trans M hM
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact h.std.stand.modU.conjInvariant g K h.std.stand.mem

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.BadStd8.toEdgeSetup
    (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    {M N : Subgroup G} {a b : G} (hM : M ∈ Ω) (hN : N ∈ omegaNbr Ω M)
    (ha : IsUniqueInvolution M a) (hb : IsUniqueInvolution N b) : EdgeSetup K z M N a b := by
  have hs := h.std
  have hΩ := hs.stand.hyp
  have hnt := T8.noTwins_of_mem hs.stand.modU.conjInvariant hs.stand.trans hs.noTwins hM
  have hec := h.eq_conjClass
  refine ⟨Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hs.stand.modU hs.stand.mem hs.hz, hint,
    ?_, ?_, ?_, Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hs.stand.modU hM ha,
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hs.stand.modU hN.1 hb, ?_⟩
  · rw [← hec]
    exact hΩ
  · rw [← hec]
    exact hM
  · rw [← hec]
    exact hN
  · intro hab
    refine hN.2.1 (hnt N ⟨hN.1, a, ha, ?_⟩)
    rw [hab]
    exact hb

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.BadStd8.exists_axis_of_triangle
    (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t) (hint : IsIntrinsicU (.sl2 3 1) K z)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (h₁ : K₁ ∈ Ω) (h12 : K₂ ∈ omegaNbr Ω K₁)
    (h13 : K₃ ∈ omegaNbr Ω K₁) (h23 : K₃ ∈ omegaNbr Ω K₂) (u₁ : IsUniqueInvolution K₁ z₁)
    (u₂ : IsUniqueInvolution K₂ z₂) (u₃ : IsUniqueInvolution K₃ z₃) (hz₃ : z₃ = z₁ * z₂) :
    ∃ (t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G), BadAxis K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ R₁ R₂ R₃ := by
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp h.std.stand.below
  exact exists_badAxis (h.toEdgeSetup hint h₁ h12 u₁ u₂) (h.toEdgeSetup hint h₁ h13 u₁ u₃)
    (h.toEdgeSetup hint h12.1 h23 u₂ u₃) hz₃ h.nonabelian hBelow

end Std

end CFSG.ClassicalInvolution.Q3.Q3AM
