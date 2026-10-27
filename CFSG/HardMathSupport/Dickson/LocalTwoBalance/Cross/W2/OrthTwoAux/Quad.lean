module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

section Singular

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {Q : QuadraticForm K W}

theorem exists_map_ne_zero_polar_ne_zero (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ finrank K W) {c : W} (hc : c ≠ 0) :
    ∃ b : W, Q b ≠ 0 ∧ polar Q c b ≠ 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨b', hb'⟩ : ∃ b', polar Q c b' ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (hQ.1 c fun y => by rw [polarBilin_apply_apply]; exact h y)
  have hQb' : Q b' = 0 := by
    by_contra h
    exact hb' (hno b' h)
  set f : W →ₗ[K] K := QuadraticMap.polarBilin Q c with hf
  have hfapp : ∀ y, f y = polar Q c y := fun y => by rw [hf, polarBilin_apply_apply]
  set U : Submodule K W := LinearMap.ker f with hU
  have hmemU : ∀ u, u ∈ U ↔ polar Q c u = 0 := fun u => by rw [hU, LinearMap.mem_ker, hfapp]
  have hQsing : ∀ u ∈ U, Q (b' + u) = 0 := by
    intro u hu
    by_contra h
    have := hno (b' + u) h
    rw [polar_add_right, (hmemU u).1 hu, add_zero] at this
    exact hb' this
  have hUiso : ∀ u ∈ U, ∀ u' ∈ U, polar Q u u' = 0 := by
    intro u hu u' hu'
    have h1 := hQsing u hu
    have h2 := hQsing u' hu'
    have h3' := hQsing (u + u') (U.add_mem hu hu')
    have e1 : Q (b' + (u + u')) = Q (b' + u) + Q u' + polar Q (b' + u) u' := by
      rw [← add_assoc]
      exact map_add_eq Q _ _
    have e2 : Q (b' + u') = Q b' + Q u' + polar Q b' u' := map_add_eq Q _ _
    have e3 : polar Q (b' + u) u' = polar Q b' u' + polar Q u u' := polar_add_left Q _ _ _
    rw [e1, e3, h1] at h3'
    rw [e2, hQb'] at h2
    linear_combination h3' - h2
  have hUdim : finrank K U + 1 = finrank K W := by
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [← hU] at hrn
    have hrange : finrank K (LinearMap.range f) = 1 := by
      apply le_antisymm
      · calc finrank K (LinearMap.range f) ≤ finrank K K := Submodule.finrank_le _
          _ = 1 := finrank_self K
      · rw [Submodule.one_le_finrank_iff]
        intro hbot
        rw [LinearMap.range_eq_bot] at hbot
        apply hb'
        rw [← hfapp, hbot]
        rfl
    omega
  have hle : U ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) U := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u' hu'
    show (QuadraticMap.polarBilin Q) u' u = 0
    rw [polarBilin_apply_apply]
    exact hUiso u' hu' u hu
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  omega

end Singular

section CardTwo

variable {K : Type*} [Field K]

theorem card_two_charP (hK : Nat.card K = 2) : CharP K 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK]; simp)

theorem card_two_cases (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  by_contra hcon
  push Not at hcon
  have h3 : ({0, 1, c} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, 1, c, zero_ne_one, hcon.1.symm, hcon.2.symm, rfl⟩
  have := Finset.card_le_univ ({0, 1, c} : Finset K)
  omega

end CardTwo

section Transvection

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_reflection_of_finrank_commSpace_eq_one (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {G : V ≃ₗ[K] V}
    (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : finrank K (commSpace G) = 1) :
    ∃ c ∈ commSpace G, Q c ≠ 0 ∧ ∀ u, G u = u + polar Q c u • c := by
  have hchar := card_two_charP hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨⟨c, hcmem⟩, hc0, hspan⟩ := finrank_eq_one_iff'.1 h1
  have hc0' : c ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hmul : ∀ v, ∃ s : K, G v - v = s • c := fun v => by
    obtain ⟨s, hs⟩ := hspan ⟨G v - v, sub_mem_commSpace G v⟩
    exact ⟨s, (congrArg Subtype.val hs).symm⟩
  have hQt : ∀ v, Q (G v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hGO
  have hpol : ∀ u v, polar Q (G u) (G v) = polar Q u v :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hGO
  obtain ⟨v₀, hv₀⟩ := mem_commSpace.mp hcmem
  have hfix : ∀ v, G v = v → polar Q v c = 0 := by
    intro v hv
    have h2' : polar Q v (G v₀) = polar Q v v₀ := by
      have := hpol v v₀
      rwa [hv] at this
    rw [← hv₀, QuadraticMap.polar_sub_right, h2', sub_self]
  have hexp : ∀ v (s : K), G v - v = s • c → s * (s * Q c + polar Q v c) = 0 := by
    intro v s hs
    have htv : G v = v + s • c := by rw [← hs]; abel
    have h2'' := hQt v
    rw [htv, map_add_eq, QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul,
      smul_eq_mul] at h2''
    linear_combination h2''
  have hQc : Q c ≠ 0 := by
    intro hQc0
    have hall : ∀ v, polar Q v c = 0 := by
      intro v
      obtain ⟨s, hs⟩ := hmul v
      by_cases hs0 : s = 0
      · rw [hs0, zero_smul, sub_eq_zero] at hs
        exact hfix v hs
      · have := hexp v s hs
        rw [hQc0, mul_zero, zero_add] at this
        exact (mul_eq_zero.mp this).resolve_left hs0
    exact hc0' (hQ.1 c fun w => by rw [polarBilin_apply_apply, polar_comm]; exact hall w)
  refine ⟨c, hcmem, hQc, fun u => ?_⟩
  obtain ⟨s, hs⟩ := hmul u
  have hQc1 : Q c = 1 := (card_two_cases hK (Q c)).resolve_left hQc
  have hs' : s = polar Q c u := by
    rcases card_two_cases hK s with rfl | rfl
    · rw [zero_smul, sub_eq_zero] at hs
      rw [polar_comm]
      exact (hfix u hs).symm
    · have := hexp u 1 hs
      rw [polar_comm]
      linear_combination h2 - this + hQc1
  have : G u = u + s • c := by rw [← hs]; abel
  rw [this, hs']

end Transvection

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux
