module

public import CFSG.LargeExtraspecial.FS77Orth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth.HypPerp

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.OrthoF2
  CFSG.RankThree.OrthogonalInvolutions
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (HypPair eichler eichler_apply eichler_mul eichler_conj
  eichler_apply_of_polar_eq_zero eichler_of_not polar_map_of_mem map_of_mem)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem finrank_perp_add_two [FiniteDimensional (ZMod 2) V] (P : HypPair Q) :
    finrank (ZMod 2) P.perp + 2 = finrank (ZMod 2) V := by
  let φ : V →ₗ[ZMod 2] ZMod 2 × ZMod 2 := (polarBilin Q P.e).prod (polarBilin Q P.f)
  have hker : LinearMap.ker φ = P.perp := by
    ext x
    rw [LinearMap.mem_ker, HypPair.mem_perp]
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1 h2
  have hrange : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    refine ⟨a • P.f + b • P.e, ?_⟩
    have h1 : polar Q P.e (a • P.f + b • P.e) = a := by
      rw [polar_add_right, polar_smul_right, polar_smul_right, P.polar_ef, P.polar_ee]
      simp
    have h2 : polar Q P.f (a • P.f + b • P.e) = b := by
      rw [polar_add_right, polar_smul_right, polar_smul_right, P.polar_ff, P.polar_fe]
      simp
    exact Prod.ext h1 h2
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange, hker, finrank_top, Module.finrank_prod, Module.finrank_self] at h
  omega

theorem eq_zero_of_mem_perp_of_mem_span (P : HypPair Q) {x : V} (hx : x ∈ P.perp)
    (hxe : x ∈ (ZMod 2) ∙ P.e) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxe
  have h := (HypPair.mem_perp.mp hx).2
  rw [polar_smul_right, P.polar_fe, smul_eq_mul, mul_one] at h
  rw [h, zero_smul]

@[expose] noncomputable def projZ (P : HypPair Q) : V →ₗ[ZMod 2] P.perp where
  toFun x := ⟨P.proj x, P.proj_mem_perp x⟩
  map_add' x y := by
    refine Subtype.ext ?_
    simp only [HypPair.proj, polar_add_left, add_smul, Submodule.coe_add]
    abel
  map_smul' c x := by
    refine Subtype.ext ?_
    simp only [HypPair.proj, polar_smul_left, smul_eq_mul, RingHom.id_apply, Submodule.coe_smul,
      smul_sub, smul_smul]

theorem coe_projZ (P : HypPair Q) (x : V) : (projZ P x : V) = P.proj x := rfl

theorem projZ_e (P : HypPair Q) : projZ P P.e = 0 := by
  refine Subtype.ext ?_
  rw [coe_projZ, HypPair.proj, P.polar_ee, P.polar_ef]
  simp

theorem projZ_smul_e (P : HypPair Q) (c : ZMod 2) : projZ P (c • P.e) = 0 := by
  rw [map_smul, projZ_e, smul_zero]

theorem eq_add_projZ (P : HypPair Q) (x : V) :
    x = polar Q x P.f • P.e + polar Q x P.e • P.f + (projZ P x : V) :=
  P.eq_add_proj x

theorem eq_add_projZ_of_polar_e (P : HypPair Q) {x : V} (hx : polar Q P.e x = 0) :
    x = polar Q x P.f • P.e + (projZ P x : V) := by
  have h := eq_add_projZ P x
  rwa [polar_comm Q x P.e, hx, zero_smul, add_zero] at h

theorem map_projZ (P : HypPair Q) {x : V} (hx : polar Q P.e x = 0) :
    Q (projZ P x : V) = Q x := by
  have h := eq_add_projZ_of_polar_e P hx
  have hp := (HypPair.mem_perp.mp (projZ P x).2).1
  conv_rhs => rw [h]
  rw [map_add_eq, map_smul_zmod2, P.Q_e, polar_smul_left, hp, mul_zero, smul_zero]
  simp

theorem coe_eichler_restrict (P : HypPair Q) (p q x : P.perp) :
    ((eichler (Q.restrict P.perp) p q x : P.perp) : V) = eichler Q (p : V) (q : V) (x : V) := by
  by_cases h : Q (p : V) = 0 ∧ polar Q (p : V) (q : V) = 0
  · have h1 : (Q.restrict P.perp) p = 0 := h.1
    have h2 : polar (Q.restrict P.perp) p q = 0 := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_restrict]
      exact h.2
    rw [eichler_apply h1 h2, eichler_apply h.1 h.2]
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
      CFSG.ClassicalGroups.Orthogonal.polar_restrict, CFSG.ClassicalGroups.Orthogonal.restrict_apply']
  · have h' : ¬ ((Q.restrict P.perp) p = 0 ∧ polar (Q.restrict P.perp) p q = 0) := by
      rw [CFSG.ClassicalGroups.Orthogonal.polar_restrict]
      exact h
    rw [eichler_of_not h, eichler_of_not h']
    rfl

theorem eichler_apply_e (P : HypPair Q) (p q : P.perp) : eichler Q (p : V) (q : V) P.e = P.e :=
  eichler_apply_of_polar_eq_zero (HypPair.mem_perp.mp p.2).1 (HypPair.mem_perp.mp q.2).1

theorem eichler_apply_f (P : HypPair Q) (p q : P.perp) : eichler Q (p : V) (q : V) P.f = P.f :=
  eichler_apply_of_polar_eq_zero (HypPair.mem_perp.mp p.2).2 (HypPair.mem_perp.mp q.2).2

variable [FiniteDimensional (ZMod 2) V]

theorem perp_fixed_eq_zero (hQ : Q.polarBilin.Nondegenerate) (P : HypPair Q)
    (h3 : 3 ≤ finrank (ZMod 2) P.perp) (τ : P.perp)
    (hτ : ∀ p q : P.perp, Q (p : V) = 0 → polar Q (p : V) (q : V) = 0 →
      eichler Q (p : V) (q : V) (τ : V) = (τ : V)) : τ = 0 := by
  refine CFSG.LargeExtraspecial.FS77.eichler_fixed_eq_zero
    (CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
      (P.polarNondegOn_perp hQ)) h3 τ (fun s u hs hsu => ?_)
  refine Subtype.ext ?_
  rw [coe_eichler_restrict]
  exact hτ s u hs (by
    rw [← CFSG.ClassicalGroups.Orthogonal.polar_restrict (Q := Q) (W := P.perp)]
    exact hsu)

theorem perp_invariant_submodule (hQ : Q.polarBilin.Nondegenerate) (P : HypPair Q)
    (h3 : 3 ≤ finrank (ZMod 2) P.perp) (W : Submodule (ZMod 2) P.perp)
    (hW : ∀ p q : P.perp, Q (p : V) = 0 → polar Q (p : V) (q : V) = 0 →
      ∀ x ∈ W, eichler (Q.restrict P.perp) p q x ∈ W) : W = ⊥ ∨ W = ⊤ :=
  CFSG.LargeExtraspecial.FS77.eichler_invariant_submodule
    (CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
      (P.polarNondegOn_perp hQ)) h3 W (fun s u hs hsu x hx =>
    hW s u hs (by
      rw [← CFSG.ClassicalGroups.Orthogonal.polar_restrict (Q := Q) (W := P.perp)]
      exact hsu) x hx)

theorem perp_invariant_quadraticForm (hQ : Q.polarBilin.Nondegenerate) (P : HypPair Q)
    (h3 : 3 ≤ finrank (ZMod 2) P.perp) (Θ : P.perp →ₗ[ZMod 2] P.perp)
    (hΘ : ∀ p q : P.perp, Q (p : V) = 0 → polar Q (p : V) (q : V) = 0 → ∀ τ,
      Q ((Θ (eichler (Q.restrict P.perp) p q τ) : P.perp) : V) = Q ((Θ τ : P.perp) : V)) :
    (∀ τ, Q ((Θ τ : P.perp) : V) = 0) ∨ (∀ τ, Q ((Θ τ : P.perp) : V) = Q (τ : V)) := by
  have h := CFSG.LargeExtraspecial.FS77.eichler_invariant_quadraticForm
    (CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict
      (P.polarNondegOn_perp hQ)) h3 ((Q.restrict P.perp).comp Θ) (fun s u hs hsu x => by
    simp only [QuadraticMap.comp_apply, CFSG.ClassicalGroups.Orthogonal.restrict_apply'] at *
    exact hΘ s u hs (by
      rw [← CFSG.ClassicalGroups.Orthogonal.polar_restrict (Q := Q) (W := P.perp)]
      exact hsu) x)
  rcases h with h | h
  · left
    intro τ
    have := congrArg (fun r : QuadraticForm (ZMod 2) P.perp => r τ) h
    simpa using this
  · right
    intro τ
    have := congrArg (fun r : QuadraticForm (ZMod 2) P.perp => r τ) h
    simpa using this

variable (hQ : Q.polarBilin.Nondegenerate)

@[expose] noncomputable def theta (P : HypPair Q) (n : V ≃ₗ[ZMod 2] V) : P.perp :=
  projZ P (n P.f - P.f)

omit [FiniteDimensional (ZMod 2) V] in
theorem theta_eichler (P : HypPair Q) {u : V} (hu : polar Q P.e u = 0) :
    theta P (eichler Q P.e u) = projZ P u := by
  unfold theta
  rw [eichler_apply_zmod2 P.Q_e hu P.f, add_assoc, add_sub_cancel_left, map_add, projZ_smul_e,
    add_zero, map_smul, P.polar_fe, one_smul]

theorem theta_mul (hQ : Q.polarBilin.Nondegenerate) (P : HypPair Q) {n n' : V ≃ₗ[ZMod 2] V}
    (hn : n ∈ pointRadical Q P.e) (hn' : n' ∈ pointRadical Q P.e) :
    theta P (n * n') = theta P n + theta P n' := by
  obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff hQ P.e_ne_zero P.Q_e).mp hn
  obtain ⟨u', hu', rfl⟩ := (mem_pointRadical_iff hQ P.e_ne_zero P.Q_e).mp hn'
  rw [eichler_mul hu hu', theta_eichler P (by rw [polar_add_right, hu, hu', add_zero]),
    theta_eichler P hu, theta_eichler P hu', map_add]

theorem theta_conj (hQ : Q.polarBilin.Nondegenerate) (P : HypPair Q) {ν n : V ≃ₗ[ZMod 2] V}
    (hν : ν ∈ orthogonalGroup Q) (hνe : ν P.e = P.e) (hn : n ∈ pointRadical Q P.e) :
    ν * n * ν⁻¹ ∈ pointRadical Q P.e ∧
      Q ((theta P (ν * n * ν⁻¹) : P.perp) : V) = Q ((theta P n : P.perp) : V) := by
  obtain ⟨u, hu, rfl⟩ := (mem_pointRadical_iff hQ P.e_ne_zero P.Q_e).mp hn
  have hνu : polar Q P.e (ν u) = 0 := by
    have h := polar_map_of_mem hν P.e u
    rw [hνe] at h
    rw [h, hu]
  have hconj : ν * eichler Q P.e u * ν⁻¹ = eichler Q P.e (ν u) := by
    rw [eichler_conj hν, hνe]
  rw [hconj]
  refine ⟨eichler_mem_pointRadical P.Q_e hνu, ?_⟩
  rw [theta_eichler P hνu, theta_eichler P hu, map_projZ P hνu, map_projZ P hu, map_of_mem hν]

end CFSG.GF2Type.Smith1980Orth.HypPerp
