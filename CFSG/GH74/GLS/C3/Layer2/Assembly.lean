module

public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS.C3.Layer2

open Subgroup

theorem nonempty_centralizer_equiv_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nonempty (↥(centralizer ({a} : Set G)) ≃* ↥(centralizer ({b} : Set G))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have key : ∀ g : G, g ∈ centralizer ({a} : Set G) → c * g * c⁻¹ ∈ centralizer ({b} : Set G) := by
    intro g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    rw [← hc]
    calc c * g * c⁻¹ * (c * a * c⁻¹) = c * (g * a) * c⁻¹ := by group
      _ = c * (a * g) * c⁻¹ := by rw [hg]
      _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group
  have key' : ∀ g : G, g ∈ centralizer ({b} : Set G) → c⁻¹ * g * c ∈ centralizer ({a} : Set G) := by
    intro g hg
    rw [mem_centralizer_singleton_iff] at hg ⊢
    have hg' : g * (c * a * c⁻¹) = (c * a * c⁻¹) * g := by rw [hc]; exact hg
    calc c⁻¹ * g * c * a = c⁻¹ * (g * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * g) * c := by rw [hg']
      _ = a * (c⁻¹ * g * c) := by group
  exact ⟨{
    toFun := fun g => ⟨c * (g : G) * c⁻¹, key g g.2⟩
    invFun := fun g => ⟨c⁻¹ * (g : G) * c, key' g g.2⟩
    left_inv := fun g => Subtype.ext (by
      show c⁻¹ * (c * (g : G) * c⁻¹) * c = (g : G)
      group)
    right_inv := fun g => Subtype.ext (by
      show c * (c⁻¹ * (g : G) * c) * c⁻¹ = (g : G)
      group)
    map_mul' := fun g h => Subtype.ext (by
      show c * ((g : G) * (h : G)) * c⁻¹ = c * (g : G) * c⁻¹ * (c * (h : G) * c⁻¹)
      group) }⟩

theorem sameCentralizerOfInvolutionPattern_of_classes {G Gs : Type*} [Group G] [Group Gs]
    [Finite G] [Finite Gs] (S : Sylow 2 G) (S' : Sylow 2 Gs)
    (φ : ↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs)) (x v : G) (x' v' : Gs)
    (hcl : ∀ u : ↥(S : Subgroup G), orderOf u = 2 → IsConj (u : G) x ∨ IsConj (u : G) v)
    (hcl' : ∀ u : ↥(S' : Subgroup Gs), orderOf u = 2 → IsConj (u : Gs) x' ∨ IsConj (u : Gs) v')
    (hφ : ∀ u : ↥(S : Subgroup G), orderOf u = 2 → (IsConj (u : G) x ↔ IsConj (φ u : Gs) x'))
    (Cx : Nonempty (↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({x'} : Set Gs))))
    (Cv : Nonempty (↥(centralizer ({v} : Set G)) ≃* ↥(centralizer ({v'} : Set Gs)))) :
    SameCentralizerOfInvolutionPattern G Gs := by
  refine ⟨S, S', φ, ?_, ?_⟩
  · intro u w hu hw
    have hφu := hφ u hu
    have hφw := hφ w hw
    have hu' : orderOf (φ u : ↥(S' : Subgroup Gs)) = 2 := by
      have h1 : orderOf (φ u) = orderOf u := MulEquiv.orderOf_eq φ u
      rw [h1]; exact hu
    have hw' : orderOf (φ w : ↥(S' : Subgroup Gs)) = 2 := by
      have h1 : orderOf (φ w) = orderOf w := MulEquiv.orderOf_eq φ w
      rw [h1]; exact hw
    constructor
    · intro hc
      by_cases hux : IsConj (u : G) x
      · have hwx : IsConj (w : G) x := hc.symm.trans hux
        exact (hφu.1 hux).trans (hφw.1 hwx).symm
      · have huv : IsConj (u : G) v := (hcl u hu).resolve_left hux
        have hwx : ¬ IsConj (w : G) x := fun h => hux (hc.trans h)
        have hwv : IsConj (w : G) v := (hcl w hw).resolve_left hwx
        have h1 : ¬ IsConj (φ u : Gs) x' := fun h => hux (hφu.2 h)
        have h2 : ¬ IsConj (φ w : Gs) x' := fun h => hwx (hφw.2 h)
        have h3 := (hcl' (φ u) hu').resolve_left h1
        have h4 := (hcl' (φ w) hw').resolve_left h2
        exact h3.trans h4.symm
    · intro hc
      by_cases hux : IsConj (φ u : Gs) x'
      · have hwx : IsConj (φ w : Gs) x' := hc.symm.trans hux
        exact (hφu.2 hux).trans (hφw.2 hwx).symm
      · have h1 : ¬ IsConj (u : G) x := fun h => hux (hφu.1 h)
        have hwx : ¬ IsConj (φ w : Gs) x' := fun h => hux (hc.trans h)
        have h2 : ¬ IsConj (w : G) x := fun h => hwx (hφw.1 h)
        have h3 := (hcl u hu).resolve_left h1
        have h4 := (hcl w hw).resolve_left h2
        exact h3.trans h4.symm
  · intro u hu
    have hφu := hφ u hu
    have hu' : orderOf (φ u : ↥(S' : Subgroup Gs)) = 2 := by
      have h1 : orderOf (φ u) = orderOf u := MulEquiv.orderOf_eq φ u
      rw [h1]; exact hu
    by_cases hux : IsConj (u : G) x
    · obtain ⟨e1⟩ := nonempty_centralizer_equiv_of_isConj hux
      obtain ⟨e2⟩ := Cx
      obtain ⟨e3⟩ := nonempty_centralizer_equiv_of_isConj (hφu.1 hux).symm
      exact ⟨(e1.trans e2).trans e3⟩
    · have huv : IsConj (u : G) v := (hcl u hu).resolve_left hux
      have h1 : ¬ IsConj (φ u : Gs) x' := fun h => hux (hφu.2 h)
      have h2 : IsConj (φ u : Gs) v' := (hcl' (φ u) hu').resolve_left h1
      obtain ⟨e1⟩ := nonempty_centralizer_equiv_of_isConj huv
      obtain ⟨e2⟩ := Cv
      obtain ⟨e3⟩ := nonempty_centralizer_equiv_of_isConj h2.symm
      exact ⟨(e1.trans e2).trans e3⟩

end CFSG.GH74.GLS.C3.Layer2
