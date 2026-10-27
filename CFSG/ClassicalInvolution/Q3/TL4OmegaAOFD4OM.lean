module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OS

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Gauss

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small

section Plane

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (GaussField F) V] [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V}
  {a : V ≃ₗ[F] V}

omit [IsScalarTower F (GaussField F) V] in
theorem polar_pair (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {u u' w w' : V}
    (h1 : polar Q u w = 0) (h2 : polar Q u' w' = 0) (h3 : polar Q u w' = 0)
    (h4 : polar Q u' w = 0) :
    polar Q (u + a u') (w + a w') = polar Q u (a w') + polar Q u' (a w) ∧
      polar Q (a (u + a u')) (w + a w') = polar Q u (a w) - polar Q u' (a w') := by
  have e1 := polar_a_right hω hg u' w
  have e2 := polar_a_right hω hg u w
  have e3 := polar_a_a hg u' w'
  have e4 := polar_a_a hg u w'
  constructor
  · rw [polar_add_left, polar_add_right, polar_add_right, e3, h1, h2, ← e1]
    ring
  · rw [map_add, a_a hω, polar_add_left, polar_add_right, polar_add_right, polar_neg_left,
      polar_neg_left, e4, h3, h4, ← e2]
    ring

end Plane

section Indep

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)] {V : Type} [AddCommGroup V]
  [Module F V] [Module (GaussField F) V] [IsScalarTower F (GaussField F) V]
  {Q : QuadraticForm F V} {a : V ≃ₗ[F] V}

theorem exists_plane_of_indep (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {x₁ x₂ : V}
    (hli : LinearIndependent (GaussField F) ![x₁, x₂])
    (h11 : gaussBilin Q hω hg x₁ x₁ = 0) (h22 : gaussBilin Q hω hg x₂ x₂ = 0)
    (h12 : gaussBilin Q hω hg x₁ x₂ = 0) :
    ∃ S : Submodule (GaussField F) V, Module.finrank (GaussField F) S = 2 ∧
      ∀ x ∈ S, gaussQuad Q hω hg x = 0 := by
  refine ⟨Submodule.span (GaussField F) (Set.range ![x₁, x₂]), ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (GaussField F)).mp hx
    have h21 : gaussBilin Q hω hg x₂ x₁ = 0 := by rw [gaussBilin_comm hω hg]; exact h12
    rw [Fin.sum_univ_two, gaussQuad_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h11, h22, h12, h21]
    ring

theorem linearIndependent_of_witness (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {x₁ x₂ z₁ z₂ : V}
    (h1 : gaussBilin Q hω hg x₁ z₁ ≠ 0) (h2 : gaussBilin Q hω hg x₂ z₁ = 0)
    (h3 : gaussBilin Q hω hg x₂ z₂ ≠ 0) :
    LinearIndependent (GaussField F) ![x₁, x₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have e1 := congrArg (fun z => gaussBilin Q hω hg z z₁) hst
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h2,
    mul_zero, add_zero, map_zero, LinearMap.zero_apply] at e1
  have hs : s = 0 := (mul_eq_zero.mp e1).resolve_right h1
  subst hs
  rw [zero_smul, zero_add] at hst
  have e2 := congrArg (fun z => gaussBilin Q hω hg z z₂) hst
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_zero, LinearMap.zero_apply] at e2
  exact ⟨rfl, (mul_eq_zero.mp e2).resolve_right h3⟩

end Indep

section Pair

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (GaussField F) V] [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V}
  {a : V ≃ₗ[F] V}

theorem exists_pair (hF : Nat.card F = 3)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) {U : Submodule F V}
    (hUp : ∀ x ∈ U, ∀ y ∈ U, polar Q x y = 0) {s t : V} (hs : s ∈ U) (ht : t ∈ U)
    (hst : polar Q s (a t) = 0) (hss : polar Q s (a s) ≠ 0) (htt : polar Q t (a t) ≠ 0) :
    ∃ x : V, gaussBilin Q hω hg x x = 0 ∧ gaussBilin Q hω hg x s ≠ 0 ∧
      (∀ w ∈ U, polar Q s (a w) = 0 → polar Q t (a w) = 0 → gaussBilin Q hω hg x w = 0) ∧
      ∃ u u' : V, u ∈ U ∧ u' ∈ U ∧ x = u + a u' ∧
        ∀ w, polar Q w (a s) = 0 → polar Q w (a t) = 0 →
          polar Q w (a u) = 0 ∧ polar Q w (a u') = 0 := by
  have hb : ∀ x y : V, polar Q x (a y) = polar Q y (a x) := fun x y => by
    rw [polar_a_right hω hg, polar_comm]
  have hts : polar Q t (a s) = 0 := by rw [hb]; exact hst
  have hβw : ∀ {u u' w : V}, u ∈ U → u' ∈ U → w ∈ U →
      gaussBilin Q hω hg (u + a u') w = ⟨polar Q u' (a w), -polar Q u (a w)⟩ := by
    intro u u' w hu hu' hw
    have h := polar_pair hω hg (w := w) (w' := 0) (hUp u hu w hw) (hUp u' hu' 0 U.zero_mem)
      (hUp u hu 0 U.zero_mem) (hUp u' hu' w hw)
    rw [map_zero, add_zero, polar_zero_right, polar_zero_right, zero_add, sub_zero] at h
    rw [gaussBilin_apply, h.1, h.2]
  have hββ : ∀ {u u' : V}, u ∈ U → u' ∈ U →
      gaussBilin Q hω hg (u + a u') (u + a u') =
        ⟨polar Q u (a u') + polar Q u' (a u), -(polar Q u (a u) - polar Q u' (a u'))⟩ := by
    intro u u' hu hu'
    have h := polar_pair hω hg (hUp u hu u hu) (hUp u' hu' u' hu') (hUp u hu u' hu')
      (hUp u' hu' u hu)
    rw [gaussBilin_apply, h.1, h.2]
  rcases Q3MFOD.cases_of_card_three hF (polar Q s (a s)) with h0 | h1 | h1
  · exact absurd h0 hss
  · rcases Q3MFOD.cases_of_card_three hF (polar Q t (a t)) with h0' | h1' | h1'
    · exact absurd h0' htt
    ·
      refine ⟨s + a t, ?_, ?_, ?_, s, t, hs, ht, rfl, fun w hws hwt => ⟨hws, hwt⟩⟩
      · rw [hββ hs ht, hst, hts, h1, h1']
        ext <;> simp
      · rw [hβw hs ht hs, hts, h1]
        intro h
        have := congrArg QuadraticAlgebra.im h
        simp at this
      · intro w hw hsw htw
        rw [hβw hs ht hw, hsw, htw]
        ext <;> simp
    ·
      refine ⟨s + t + a 0, ?_, ?_, ?_, s + t, 0, U.add_mem hs ht, U.zero_mem, rfl,
        fun w hws hwt => ⟨by rw [map_add, polar_add_right, hws, hwt, add_zero], by
          rw [map_zero, polar_zero_right]⟩⟩
      · rw [hββ (U.add_mem hs ht) U.zero_mem]
        rw [map_zero, polar_zero_right, polar_zero_left, map_add, polar_add_left, polar_add_right,
          polar_add_right, h1, h1', hst, hts]
        ext <;> simp
      · rw [hβw (U.add_mem hs ht) U.zero_mem hs, polar_zero_left, polar_add_left, h1, hts]
        intro h
        have := congrArg QuadraticAlgebra.im h
        simp at this
      · intro w hw hsw htw
        rw [hβw (U.add_mem hs ht) U.zero_mem hw, polar_zero_left, polar_add_left, hsw, htw]
        ext <;> simp
  · rcases Q3MFOD.cases_of_card_three hF (polar Q t (a t)) with h0' | h1' | h1'
    · exact absurd h0' htt
    ·
      refine ⟨s + t + a 0, ?_, ?_, ?_, s + t, 0, U.add_mem hs ht, U.zero_mem, rfl,
        fun w hws hwt => ⟨by rw [map_add, polar_add_right, hws, hwt, add_zero], by
          rw [map_zero, polar_zero_right]⟩⟩
      · rw [hββ (U.add_mem hs ht) U.zero_mem]
        rw [map_zero, polar_zero_right, polar_zero_left, map_add, polar_add_left, polar_add_right,
          polar_add_right, h1, h1', hst, hts]
        ext <;> simp
      · rw [hβw (U.add_mem hs ht) U.zero_mem hs, polar_zero_left, polar_add_left, h1, hts]
        intro h
        have := congrArg QuadraticAlgebra.im h
        simp at this
      · intro w hw hsw htw
        rw [hβw (U.add_mem hs ht) U.zero_mem hw, polar_zero_left, polar_add_left, hsw, htw]
        ext <;> simp
    ·
      refine ⟨s + a t, ?_, ?_, ?_, s, t, hs, ht, rfl, fun w hws hwt => ⟨hws, hwt⟩⟩
      · rw [hββ hs ht, hst, hts, h1, h1']
        ext <;> simp
      · rw [hβw hs ht hs, hts, h1]
        intro h
        have := congrArg QuadraticAlgebra.im h
        simp at this
      · intro w hw hsw htw
        rw [hβw hs ht hw, hsw, htw]
        ext <;> simp

end Pair

end CFSG.ClassicalInvolution.Q3.TL4.Gauss
