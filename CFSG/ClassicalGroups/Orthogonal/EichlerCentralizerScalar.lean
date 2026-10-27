module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_eq_smul_of_commute_eichler [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (hA : ∃ w ∈ P.perp, Q w ≠ 0) (Y : V →+ V)
    (he : ∀ w ∈ P.perp, ∀ x, Y (eichler Q P.e w x) = eichler Q P.e w (Y x))
    (hf : ∀ w ∈ P.perp, ∀ x, Y (eichler Q P.f w x) = eichler Q P.f w (Y x)) :
    ∃ μ : K, ∀ x, Y x = μ • x := by
  classical
  have fixed_aux : ∀ (u v : V), Q u = 0 → Q v = 0 → polar Q u v = 1 →
      (∃ w, polar Q u w = 0 ∧ polar Q v w = 0 ∧ Q w ≠ 0) →
      ∀ y : V, (∀ w, polar Q u w = 0 → polar Q v w = 0 → eichler Q u w y = y) →
        y ∈ Submodule.span K {u} := by
    intro u v hu hv huv hP y hy
    let P' : HypPair Q := ⟨u, v, hu, hv, huv⟩
    obtain ⟨w₀, hw₀u, hw₀v, hQw₀⟩ := hP
    have hw₀ : w₀ ∈ P'.perp := by
      rw [HypPair.mem_perp]
      exact ⟨hw₀u, hw₀v⟩
    have hu_ne : u ≠ 0 := by
      rintro rfl
      rw [polar_zero_left] at huv
      exact zero_ne_one huv
    have hw₀_ne : w₀ ≠ 0 := by
      rintro rfl
      exact hQw₀ (QuadraticMap.map_zero Q)
    have hw₀_not : w₀ ∉ Submodule.span K {u} := by
      intro hmem
      rw [Submodule.mem_span_singleton] at hmem
      obtain ⟨a, ha⟩ := hmem
      have h1 : polar Q v w₀ = 0 := hw₀v
      rw [← ha, polar_smul_right_eq, polar_comm Q v u, huv, mul_one] at h1
      exact hw₀_ne (by rw [← ha, h1, zero_smul])
    have hBe : polar Q y u = 0 := by
      by_contra hne
      have h := hy w₀ hw₀u hw₀v
      rw [eichler_apply hu hw₀u] at h
      have hEq : polar Q y u • w₀ =
          (polar Q y w₀ + Q w₀ * polar Q y u) • u := by
        linear_combination (norm := module) h
      have hw₀_eq : w₀ =
          ((polar Q y u)⁻¹ * (polar Q y w₀ + Q w₀ * polar Q y u)) • u := by
        calc w₀ = ((polar Q y u)⁻¹ * polar Q y u) • w₀ := by
              rw [inv_mul_cancel₀ hne, one_smul]
          _ = (polar Q y u)⁻¹ • (polar Q y u • w₀) := by rw [mul_smul]
          _ = (polar Q y u)⁻¹ •
                ((polar Q y w₀ + Q w₀ * polar Q y u) • u) := by rw [hEq]
          _ = ((polar Q y u)⁻¹ *
                (polar Q y w₀ + Q w₀ * polar Q y u)) • u := by rw [smul_smul]
      exact hw₀_not (Submodule.mem_span_singleton.mpr ⟨_, hw₀_eq.symm⟩)
    have hperp : ∀ w, polar Q u w = 0 → polar Q v w = 0 → polar Q y w = 0 := by
      intro w hwu hwv
      have h := hy w hwu hwv
      rw [eichler_apply hu hwu, hBe] at h
      have h1 : polar Q y w • u = 0 := by
        linear_combination (norm := module) -h
      rcases smul_eq_zero.mp h1 with h0 | h0
      · exact h0
      · exact absurd h0 hu_ne
    have hproj : P'.proj y = 0 := by
      refine P'.polarNondegOn_perp hQ (P'.proj y) (P'.proj_mem_perp y) ?_
      intro z hz
      rw [HypPair.mem_perp] at hz
      have hyz : polar Q y z = 0 := hperp z hz.1 hz.2
      rw [HypPair.proj, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
        hyz, hz.1, hz.2]
      ring
    have hy_eq : y = polar Q y v • u := by
      conv_lhs => rw [P'.eq_add_proj y]
      rw [hBe, hproj, zero_smul, add_zero, add_zero]
    rw [hy_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hAe : ∃ w, polar Q P.e w = 0 ∧ polar Q P.f w = 0 ∧ Q w ≠ 0 := by
    obtain ⟨w, hw, hQw⟩ := hA
    exact ⟨w, (HypPair.mem_perp.mp hw).1, (HypPair.mem_perp.mp hw).2, hQw⟩
  have hAf : ∃ w, polar Q P.f w = 0 ∧ polar Q P.e w = 0 ∧ Q w ≠ 0 := by
    obtain ⟨w, hw, hQw⟩ := hA
    exact ⟨w, (HypPair.mem_perp.mp hw).2, (HypPair.mem_perp.mp hw).1, hQw⟩
  have fixed_e := fixed_aux P.e P.f P.Q_e P.Q_f P.polar_ef hAe
  have fixed_f := fixed_aux P.f P.e P.Q_f P.Q_e (by rw [polar_comm, P.polar_ef]) hAf
  have hYmem_e : ∀ s : K, Y (s • P.e) ∈ Submodule.span K {P.e} := by
    intro s
    refine fixed_e _ ?_
    intro w hwu hwv
    rw [← he w (by rw [HypPair.mem_perp]; exact ⟨hwu, hwv⟩) (s • P.e), map_smul,
      eichler_apply_self]
  have hYmem_f : ∀ s : K, Y (s • P.f) ∈ Submodule.span K {P.f} := by
    intro s
    refine fixed_f _ ?_
    intro w hwv hwu
    rw [← hf w (by rw [HypPair.mem_perp]; exact ⟨hwu, hwv⟩) (s • P.f), map_smul,
      eichler_apply_self]
  have hex_e : ∀ s : K, ∃ a : K, Y (s • P.e) = a • P.e := by
    intro s
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hYmem_e s)
    exact ⟨a, ha.symm⟩
  choose φ hφ using hex_e
  have hex_f : ∀ s : K, ∃ a : K, Y (s • P.f) = a • P.f := by
    intro s
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hYmem_f s)
    exact ⟨a, ha.symm⟩
  choose ψ hψ using hex_f
  have hYw_e : ∀ (w : V), w ∈ P.perp → ∀ s : K,
      Y (s • w) = ψ s • w + (φ (s * Q w) - ψ s * Q w) • P.e := by
    intro w hw s
    have hw1 : polar Q P.e w = 0 := (HypPair.mem_perp.mp hw).1
    have hw2 : polar Q P.f w = 0 := (HypPair.mem_perp.mp hw).2
    have hE : eichler Q P.e w (s • P.f) = s • P.f + s • w - (s * Q w) • P.e := by
      rw [eichler_apply P.Q_e hw1, polar_smul_left_eq, polar_smul_left_eq, P.polar_fe,
        mul_one, hw2, mul_zero, zero_add, mul_comm (Q w) s]
    have hE2 : eichler Q P.e w (ψ s • P.f) =
        ψ s • P.f + ψ s • w - (Q w * ψ s) • P.e := by
      rw [eichler_apply P.Q_e hw1, polar_smul_left_eq, polar_smul_left_eq, P.polar_fe,
        mul_one, hw2, mul_zero, zero_add]
    have hL : Y (eichler Q P.e w (s • P.f)) =
        ψ s • P.f + Y (s • w) - φ (s * Q w) • P.e := by
      rw [hE, map_sub, map_add, hψ s, hφ (s * Q w)]
    have hR : eichler Q P.e w (Y (s • P.f)) =
        ψ s • P.f + ψ s • w - (Q w * ψ s) • P.e := by
      rw [hψ s, hE2]
    have h := he w hw (s • P.f)
    rw [hL, hR] at h
    linear_combination (norm := module) h
  have hYw_f : ∀ (w : V), w ∈ P.perp → ∀ s : K,
      Y (s • w) = φ s • w + (ψ (s * Q w) - φ s * Q w) • P.f := by
    intro w hw s
    have hw1 : polar Q P.e w = 0 := (HypPair.mem_perp.mp hw).1
    have hw2 : polar Q P.f w = 0 := (HypPair.mem_perp.mp hw).2
    have hE : eichler Q P.f w (s • P.e) = s • P.e + s • w - (s * Q w) • P.f := by
      rw [eichler_apply P.Q_f hw2, polar_smul_left_eq, polar_smul_left_eq, P.polar_ef,
        mul_one, hw1, mul_zero, zero_add, mul_comm (Q w) s]
    have hE2 : eichler Q P.f w (φ s • P.e) =
        φ s • P.e + φ s • w - (Q w * φ s) • P.f := by
      rw [eichler_apply P.Q_f hw2, polar_smul_left_eq, polar_smul_left_eq, P.polar_ef,
        mul_one, hw1, mul_zero, zero_add]
    have hL : Y (eichler Q P.f w (s • P.e)) =
        φ s • P.e + Y (s • w) - ψ (s * Q w) • P.f := by
      rw [hE, map_sub, map_add, hφ s, hψ (s * Q w)]
    have hR : eichler Q P.f w (Y (s • P.e)) =
        φ s • P.e + φ s • w - (Q w * φ s) • P.f := by
      rw [hφ s, hE2]
    have h := hf w hw (s • P.e)
    rw [hL, hR] at h
    linear_combination (norm := module) h
  obtain ⟨w₀, hw₀, hQw₀⟩ := hA
  have hw₀_ne : w₀ ≠ 0 := by
    rintro rfl
    exact hQw₀ (QuadraticMap.map_zero Q)
  have hcomp : ∀ s : K,
      ψ s • w₀ + (φ (s * Q w₀) - ψ s * Q w₀) • P.e =
        φ s • w₀ + (ψ (s * Q w₀) - φ s * Q w₀) • P.f := by
    intro s
    rw [← hYw_e w₀ hw₀ s, hYw_f w₀ hw₀ s]
  have hcoeff_f : ∀ s : K, φ (s * Q w₀) - ψ s * Q w₀ = 0 := by
    intro s
    have h := congrArg (fun z => polar Q z P.f) (hcomp s)
    simp only [polar_add_left, polar_smul_left_eq, polar_comm Q w₀ P.f,
      (HypPair.mem_perp.mp hw₀).2, P.polar_ef, P.polar_ff, mul_zero, mul_one, add_zero,
      zero_add] at h
    exact h
  have hcoeff_e : ∀ s : K, ψ (s * Q w₀) - φ s * Q w₀ = 0 := by
    intro s
    have h := congrArg (fun z => polar Q z P.e) (hcomp s)
    simp only [polar_add_left, polar_smul_left_eq, polar_comm Q w₀ P.e,
      (HypPair.mem_perp.mp hw₀).1, P.polar_ee, P.polar_fe, mul_zero, mul_one, add_zero,
      zero_add] at h
    exact h.symm
  have hpsi : ∀ s : K, ψ s = φ s := by
    intro s
    have hw : (ψ s - φ s) • w₀ = 0 := by
      have h := hcomp s
      rw [hcoeff_f s, hcoeff_e s] at h
      rw [zero_smul, add_zero, zero_smul, add_zero] at h
      rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hw with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw₀_ne
  have hef_ne : P.e - P.f ≠ 0 := by
    intro h
    have h' : P.e = P.f := sub_eq_zero.mp h
    have h2 : polar Q P.e P.f = 0 := by
      rw [h']
      exact P.polar_ff
    rw [P.polar_ef] at h2
    exact one_ne_zero h2
  have hrel : ∀ (w : V), w ∈ P.perp → ∀ s : K,
      Y (s • w) = φ s • w ∧ φ (s * Q w) = φ s * Q w := by
    intro w hw s
    have h1 := hYw_e w hw s
    have h2 := hYw_f w hw s
    rw [hpsi s] at h1
    rw [hpsi (s * Q w)] at h2
    have hcoe : (φ (s * Q w) - φ s * Q w) • P.e =
        (φ (s * Q w) - φ s * Q w) • P.f := add_left_cancel (h1.symm.trans h2)
    have hA0 : φ (s * Q w) - φ s * Q w = 0 := by
      have h : (φ (s * Q w) - φ s * Q w) • (P.e - P.f) = 0 := by
        rw [smul_sub, hcoe, sub_self]
      rcases smul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hef_ne
    refine ⟨?_, sub_eq_zero.mp hA0⟩
    rw [h1, hA0, zero_smul, add_zero]
  have hQrel : ∀ (w : V), w ∈ P.perp → ∀ s : K, φ (s * Q w) = φ s * Q w :=
    fun w hw s => (hrel w hw s).2
  have hphi : ∀ s : K, φ s = φ 1 * s := by
    intro s
    obtain ⟨t, ht⟩ : ∃ t : K, t * Q w₀ = s :=
      ⟨s * (Q w₀)⁻¹, by rw [mul_assoc, inv_mul_cancel₀ hQw₀, mul_one]⟩
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' t
    have hmem : r • w₀ ∈ P.perp := P.perp.smul_mem r hw₀
    have h := hQrel (r • w₀) hmem 1
    rw [one_mul, map_smul_eq_sq, pow_two, ← hr, ht] at h
    exact h
  refine ⟨φ 1, fun x => ?_⟩
  have hYproj : Y (P.proj x) = φ 1 • P.proj x := by
    have h := (hrel (P.proj x) (P.proj_mem_perp x) 1).1
    simpa using h
  have hYe : ∀ a : K, Y (a • P.e) = φ 1 • (a • P.e) := by
    intro a
    rw [hφ a, hphi a, mul_smul]
  have hYf : ∀ b : K, Y (b • P.f) = φ 1 • (b • P.f) := by
    intro b
    rw [hψ b, hpsi b, hphi b, mul_smul]
  calc Y x = Y (polar Q x P.f • P.e + polar Q x P.e • P.f + P.proj x) := by
        conv_lhs => rw [P.eq_add_proj x]
    _ = Y (polar Q x P.f • P.e) + Y (polar Q x P.e • P.f) + Y (P.proj x) := by
        rw [map_add, map_add]
    _ = φ 1 • (polar Q x P.f • P.e) + φ 1 • (polar Q x P.e • P.f) +
          φ 1 • P.proj x := by
        rw [hYe, hYf, hYproj]
    _ = φ 1 • (polar Q x P.f • P.e + polar Q x P.e • P.f + P.proj x) := by
        rw [smul_add, smul_add]
    _ = φ 1 • x := by conv_rhs => rw [P.eq_add_proj x]

section Minus

variable {K : Type} [Field K]

theorem eichler_mem_statedOmega_quadMinus [Finite K] [CharP K 2] {m : ℕ} {b c : K}
    (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (u w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).symm
        (eichler (quadMinus m K b c) u w) ∈ StatedOmega (StatedQuadMinus m K b c) := by
  rw [statedOmega_quadMinus_eq_map_of_two_le hm hirr]
  exact Subgroup.mem_map_of_mem
    ((toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).symm.toMonoidHom)
    (eichler_mem_elementaryGroup (quadMinus m K b c) u w)

theorem exists_mem_statedOmega_quadMinus_eichler [Finite K] [CharP K 2] {m : ℕ} {b c : K}
    (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (u w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    ∃ A ∈ StatedOmega (StatedQuadMinus m K b c),
      ∀ x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
        ((A : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
            Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
              (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ x =
          eichler (quadMinus m K b c) u w x := by
  refine ⟨(toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).symm
      (eichler (quadMinus m K b c) u w),
    eichler_mem_statedOmega_quadMinus hm hirr u w, ?_⟩
  intro x
  rw [← toLinEquiv_apply ((toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).symm
    (eichler (quadMinus m K b c) u w)) x, MulEquiv.apply_symm_apply]

end Minus

end CFSG.ClassicalGroups.Orthogonal

