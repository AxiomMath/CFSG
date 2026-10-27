module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.NormalCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndSchur

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem SylowEnd.ncard_le_of_fibers {X F K : Set G} (φ : G → G) (hF : ∀ x ∈ X, φ x ∈ F)
    (hfib : ∀ x ∈ X, ∀ x' ∈ X, φ x = φ x' → x⁻¹ * x' ∈ K) : X.ncard ≤ F.ncard * K.ncard := by
  classical
  let rep : G → G := fun a => if h : ∃ x ∈ X, φ x = a then h.choose else 1
  have hrep : ∀ x ∈ X, rep (φ x) ∈ X ∧ φ (rep (φ x)) = φ x := by
    intro x hx
    have h : ∃ x' ∈ X, φ x' = φ x := ⟨x, hx, rfl⟩
    have : rep (φ x) = h.choose := dite_eq_left h
    rw [this]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  let g : G → G × G := fun x => (φ x, (rep (φ x))⁻¹ * x)
  have hmaps : ∀ x ∈ X, g x ∈ F ×ˢ K := fun x hx =>
    ⟨hF x hx, hfib _ (hrep x hx).1 x hx (hrep x hx).2⟩
  have hinj : Set.InjOn g X := by
    intro x hx x' hx' h
    have h1 : φ x = φ x' := (Prod.ext_iff.1 h).1
    have h2 : (rep (φ x))⁻¹ * x = (rep (φ x'))⁻¹ * x' := (Prod.ext_iff.1 h).2
    rw [h1] at h2
    exact mul_left_cancel h2
  calc X.ncard ≤ (F ×ˢ K).ncard :=
        Set.ncard_le_ncard_of_injOn g hmaps hinj (Set.toFinite _)
    _ = F.ncard * K.ncard := Set.ncard_prod

end CFSG.EvenSporadicStandard.ThStd
