module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Certified
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionExists
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionPerfect
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Inv

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification CFSG.Open
open scoped commutatorElement

section Facts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem Hyp.odd_inf (h : Hyp G A) : Odd (Nat.card ↥(A ⊓ centralizer (A : Set G))) := by
  have hcard : Nat.card ↥(A ⊓ centralizer (A : Set G)) = Nat.card ↥(center ↥A) := by
    rw [← map_center_subtype_eq_inf_centralizer A]
    exact Subgroup.card_map_of_injective A.subtype_injective
  rw [hcard]
  exact h.odd

theorem Hyp.exists_radicals_of_isSylowOf (h : Hyp G A)
    {V : Subgroup G} (hV : IsSylowOf 2 V A) : ∃ V₁ V₂ : Subgroup G, Radicals V V₁ V₂ := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  obtain ⟨V₁, V₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    exists_parabolic_radicals_of_isSylowOf h.odd e hV
  exact ⟨V₁, V₂, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩⟩

theorem Hyp.facts
    (h : Hyp G A) : Facts A := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  refine ⟨h.odd_inf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hx2 hy2
    exact involutions_conj_of_mem h.odd e hx hy hx2 hy2
  · intro E hEN hE hcard
    exact le_sup_centralizer_of_sixteen_le_inf h.commutator_eq_top e hEN hE hcard
  · intro V hV
    exact centralizer_V_le_of_certificate h.commutator_eq_top e hV
  · intro V hV
    exact h.exists_radicals_of_isSylowOf hV
  · intro y hy hy2 hout c hc hc2
    exact (outer_involution_cases_of_certificate h.commutator_eq_top h.odd e hy hy2 hout).1 c hc hc2
  · intro y hy hy2 hout hns
    exact exists_perfect_involution_of_outer_of_certificate h.commutator_eq_top h.odd e hy hy2
      hout hns
  · intro D hDN hD c hc hc2
    exact mem_of_mul_self_of_perfect h.commutator_eq_top e h.cyc hDN hD hc hc2

theorem Hyp.exists_radicals (h : Hyp G A) (d : Datum A) :
    ∃ V₁ V₂ : Subgroup G, Radicals d.V V₁ V₂ :=
  h.exists_radicals_of_isSylowOf d.V_isSylow

end Facts

section Gamma

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {V₁ V₂ : Subgroup G}

theorem Hyp.adj_properties (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) :
    W ⊔ zpowers d.t ≤ d.P ∧ IsElemAbelian 2 (W ⊔ zpowers d.t) ∧
      Nat.card ↥(W ⊔ zpowers d.t) = 32 :=
  h.facts.adj_properties d hR hW

theorem Hyp.card_elem_eq_iff (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    {E : Subgroup G} (hEP : E ≤ d.P) (hE : IsElemAbelian 2 E) :
    Nat.card E = 32 ↔ E = V₁ ⊔ zpowers d.t ∨ E = V₂ ⊔ zpowers d.t :=
  h.facts.card_elem_eq_iff d hR hEP hE

theorem Hyp.card_elem_le (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    {E : Subgroup G} (hEP : E ≤ d.P) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 32 :=
  h.facts.card_elem_le d hR hEP hE

end Gamma

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

@[expose] def UnitaryResidualFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Hyp G A → ∀ d : Datum A,
    (∀ Q : Subgroup G, IsPGroup 2 Q → d.P ≤ Q → Q = d.P) →
    (∃ t' ∈ d.P, IsConj d.t t' ∧ t' ≠ d.t) →
    (∀ t' ∈ d.P, IsConj d.t t' → t' ≠ d.t →
      t' ∉ A ⊔ centralizer (A : Set G) ∧ Group.IsSolvable ↥(A ⊓ centralizer ({t'} : Set G))) →
    False

theorem alpha
    (hres : UnitaryResidualFalse)
    (h : Hyp G A) (d : Datum A) :
    ∃ t' ∈ d.P ⊓ centralizer (d.P : Set G), IsConj d.t t' ∧ t' ≠ d.t := by
  by_contra hno
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  obtain ⟨hmax, hex, hres'⟩ :=
    h.facts.residual_conf_of_not_alpha d hR (d.exists_conj_commuting h) hno
  exact hres G A h d hmax hex hres'

end Main

end CFSG.OddStandard.Seitz77
