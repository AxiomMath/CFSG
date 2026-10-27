module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Clique

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjugate_inv_mul_self_of_mem_centralizer {u c : G}
    (hc : c ∈ Subgroup.centralizer ({u} : Set G)) : c⁻¹ * u * c = u := by
  have := mem_centralizer_single.1 hc
  calc c⁻¹ * u * c = c⁻¹ * (u * c) := by group
    _ = c⁻¹ * (c * u) := by rw [this]
    _ = u := by group

omit [Finite G] in
theorem conjugate_centralizer_of_mem {u c : G} (hc : c ∈ Subgroup.centralizer ({u} : Set G)) :
    conjugate (Subgroup.centralizer ({u} : Set G)) c = Subgroup.centralizer ({u} : Set G) := by
  rw [conjugate_centralizer_singleton, conjugate_inv_mul_self_of_mem_centralizer hc]

theorem rel_conjugate_of_involution {A B B₂ : Subgroup G} (hA : QS A) (hs : Star A)
    (hB : B ∈ ConjCl A) (hB₂ : B₂ ∈ ConjCl A) (hcomm : ⁅B, B₂⁆ = ⊥) {u c : G}
    (hu : orderOf u = 2) (huB : u ∈ B) (hc : c ∈ Subgroup.centralizer ({u} : Set G)) :
    Rel B (conjugate B c) := by
  have hB₂C : B₂ ≤ Subgroup.centralizer ({u} : Set G) := by
    have h1 : B₂ ≤ Subgroup.centralizer (B : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    exact h1.trans (Subgroup.centralizer_le (by simpa using huB))
  have h₂ : IsCompIn B₂ (Subgroup.centralizer ({u} : Set G)) :=
    isCompIn_centralizer_involution (ConjCl.qs hA hB₂) (ConjCl.star hs hB₂) hu hB₂C
  have h₂c := h₂.cj c
  rw [conjugate_centralizer_of_mem hc] at h₂c
  have hrel₂ : Rel B₂ (conjugate B₂ c) := by
    by_cases hne : B₂ = conjugate B₂ c
    · exact Or.inl hne
    · exact Or.inr (commute_of_isCompIn_ne h₂ h₂c hne)
  have hBc : conjugate B c ∈ ConjCl A := ConjCl.cj hB c
  have hB₂c : conjugate B₂ c ∈ ConjCl A := ConjCl.cj hB₂ c
  have r1 : Rel B B₂ := Or.inr hcomm
  have r2 : Rel B (conjugate B₂ c) := Rel.trans' hA hs hB hB₂ hB₂c r1 hrel₂
  have r3 : Rel (conjugate B₂ c) (conjugate B c) := (r1.cj c).symm
  exact Rel.trans' hA hs hB hB₂c hBc r2 r3

theorem conjugate_eq_of_noncentral {A B B₂ : Subgroup G} (hA : QS A) (hs : Star A)
    (hB : B ∈ ConjCl A) (hB₂ : B₂ ∈ ConjCl A) (hcomm : ⁅B, B₂⁆ = ⊥) {u c : G}
    (hu : orderOf u = 2) (huB : u ∈ B) (hnc : u ∉ Subgroup.centralizer (B : Set G))
    (hc : c ∈ Subgroup.centralizer ({u} : Set G)) : conjugate B c = B := by
  rcases rel_conjugate_of_involution hA hs hB hB₂ hcomm hu huB hc with h | h
  · exact h.symm
  · exfalso
    apply hnc
    have huBc : u ∈ conjugate B c := by
      rw [mem_conjugate]
      have := mem_centralizer_single.1 hc
      have e : c * u * c⁻¹ = u := by
        calc c * u * c⁻¹ = (c * u) * c⁻¹ := rfl
          _ = (u * c) * c⁻¹ := by rw [this]
          _ = u := by group
      rw [e]
      exact huB
    have hle : conjugate B c ≤ Subgroup.centralizer (B : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h
    exact hle huBc

theorem centralizer_le_normalizer_Dgrp {A B B₂ : Subgroup G} (hA : QS A) (hs : Star A)
    (hB : B ∈ ConjCl A) (hB₂ : B₂ ∈ ConjCl A) (hcomm : ⁅B, B₂⁆ = ⊥) {u : G}
    (hu : orderOf u = 2) (huB : u ∈ B) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (Dgrp A B : Set G) := fun _ hc =>
  mem_normalizer_Dgrp_of_rel' hA hs hB (rel_conjugate_of_involution hA hs hB hB₂ hcomm hu huB hc)

theorem centralizer_le_normalizer_of_noncentral {A B B₂ : Subgroup G} (hA : QS A) (hs : Star A)
    (hB : B ∈ ConjCl A) (hB₂ : B₂ ∈ ConjCl A) (hcomm : ⁅B, B₂⁆ = ⊥) {u : G}
    (hu : orderOf u = 2) (huB : u ∈ B) (hnc : u ∉ Subgroup.centralizer (B : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (B : Set G) := fun _ hc =>
  mem_normalizer_of_conjugate_eq (conjugate_eq_of_noncentral hA hs hB hB₂ hcomm hu huB hnc hc)

end CFSG.CGT.PushingUpLit.CGT6.Nine7
