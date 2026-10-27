module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

universe u

namespace CFSG.QuasithinUnique.Setup.X7

section Unipotent

variable {K : Type*} [Group K] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem add_self_eq_zero_of_zmod_two (y : U) : y + y = 0 := by
  rw [← two_nsmul]
  exact p_nsmul_eq_zero_of_charP (p := 2) (ZMod 2) y

theorem eq_one_of_trivial_on_sub_and_quotient (ρ : Representation (ZMod 2) K U) {k : K}
    (hk : Odd (orderOf k)) (X : Submodule (ZMod 2) U) (h1 : ∀ x ∈ X, ρ k x = x)
    (h2 : ∀ u, ρ k u - u ∈ X) : ρ k = 1 := by
  have hsq : ρ k * ρ k = 1 := by
    refine LinearMap.ext fun u => ?_
    have hy := h1 _ (h2 u)
    rw [map_sub] at hy
    have hz : ρ k (ρ k u) = u := by
      have h3 : ρ k (ρ k u) - ρ k u = ρ k u - u := hy
      have h4 : ρ k (ρ k u) = ρ k u + (ρ k u - u) := by rw [← h3]; abel
      rw [h4]
      have h5 := add_self_eq_zero_of_zmod_two (ρ k u - u)
      calc ρ k u + (ρ k u - u) = (ρ k u - u) + (ρ k u - u) + u := by abel
        _ = u := by rw [h5, zero_add]
    exact hz
  obtain ⟨j, hj⟩ := hk
  have hpow : (ρ k) ^ orderOf k = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hj, pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at hpow
  exact hpow

end Unipotent

section Ranks

variable {K : Type*} [Group K] {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
  {ρ : Representation (ZMod 2) K U}

theorem finrank_range_toRepresentation_le (Xs : Subrepresentation ρ) (g : K) :
    Module.finrank (ZMod 2) (LinearMap.range (Xs.toRepresentation g - 1)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := by
  have h : (LinearMap.range (Xs.toRepresentation g - 1)).map Xs.toSubmodule.subtype ≤
      LinearMap.range (ρ g - 1) := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(y : U), rfl⟩
  calc Module.finrank (ZMod 2) (LinearMap.range (Xs.toRepresentation g - 1))
      = Module.finrank (ZMod 2)
          ((LinearMap.range (Xs.toRepresentation g - 1)).map Xs.toSubmodule.subtype) :=
        LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective _ Xs.toSubmodule.injective_subtype _)
    _ ≤ _ := Submodule.finrank_mono h

theorem finrank_range_quotient_le (Xs : Subrepresentation ρ) (g : K) :
    Module.finrank (ZMod 2) (LinearMap.range (Xs.quotient g - 1)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := by
  have h : LinearMap.range (Xs.quotient g - 1) ≤
      (LinearMap.range (ρ g - 1)).map Xs.toSubmodule.mkQ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨(ρ g - 1) u, ⟨u, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono h).trans (Submodule.finrank_map_le _ _)

end Ranks

theorem exists_irreducible_subquotient {K : Type*} [Group K] (n : ℕ) :
    ∀ {U : Type u} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
      (ρ : Representation (ZMod 2) K U) (k : K), Module.finrank (ZMod 2) U = n →
      Odd (orderOf k) → ρ k ≠ 1 →
      ∃ (Y : Type u) (_ : AddCommGroup Y) (_ : Module (ZMod 2) Y) (_ : Finite Y)
        (σ : Representation (ZMod 2) K Y), σ.IsIrreducible ∧ σ k ≠ 1 ∧
          ∀ g : K, Module.finrank (ZMod 2) (LinearMap.range (σ g - 1)) ≤
            Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U _ _ _ ρ k hn hk hρ
    have hU : Nontrivial U := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hρ (LinearMap.ext fun u => Subsingleton.elim _ _)
    by_cases hirr : ρ.IsIrreducible
    · exact ⟨U, inferInstance, inferInstance, inferInstance, ρ, hirr, hρ, fun g => le_rfl⟩
    · rw [isIrreducible_iff] at hirr
      push Not at hirr
      obtain ⟨X, hXinv, hXbot, hXtop⟩ := hirr hU
      let Xs : Subrepresentation ρ := ⟨X, fun g v hv => hXinv g v hv⟩
      have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
      by_cases hX1 : ∃ x ∈ X, ρ k x ≠ x
      · have hlt : Module.finrank (ZMod 2) X < n := by
          rw [← hn]
          exact Submodule.finrank_lt hXtop
        obtain ⟨Y, i1, i2, i3, σ, h1, h2, h3⟩ := ih _ hlt (U := ↥X) Xs.toRepresentation k rfl hk (by
          intro h
          obtain ⟨x, hx, hne⟩ := hX1
          apply hne
          have := LinearMap.congr_fun h ⟨x, hx⟩
          exact congrArg Subtype.val this)
        exact ⟨Y, i1, i2, i3, σ, h1, h2, fun g => (h3 g).trans (finrank_range_toRepresentation_le Xs g)⟩
      · push Not at hX1
        have hlt : Module.finrank (ZMod 2) (U ⧸ X) < n := by
          have h1 := Submodule.finrank_quotient_add_finrank X
          have h2 : 1 ≤ Module.finrank (ZMod 2) X := Submodule.one_le_finrank_iff.mpr hXbot
          omega
        have hQfin : Finite (U ⧸ X) :=
          Finite.of_surjective Submodule.Quotient.mk (Submodule.Quotient.mk_surjective X)
        obtain ⟨Y, i1, i2, i3, σ, h1, h2, h3⟩ := ih _ hlt (U := U ⧸ X) Xs.quotient k rfl hk (by
          intro h
          apply hρ
          refine eq_one_of_trivial_on_sub_and_quotient ρ hk X hX1 fun u => ?_
          have h3 : (Submodule.Quotient.mk (ρ k u) : U ⧸ X) = Submodule.Quotient.mk u :=
            LinearMap.congr_fun h (Submodule.Quotient.mk u)
          exact (Submodule.Quotient.eq X).mp h3)
        exact ⟨Y, i1, i2, i3, σ, h1, h2, fun g => (h3 g).trans (finrank_range_quotient_le Xs g)⟩

end CFSG.QuasithinUnique.Setup.X7
