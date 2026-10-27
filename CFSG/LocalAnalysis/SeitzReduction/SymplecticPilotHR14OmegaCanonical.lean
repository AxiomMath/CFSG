module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaO2Even

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.OrthogonalInvolutions (commSpace natCast_finrank_commSpace_mul
  even_finrank_commSpace_of_forall_eq_zero)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  [Finite K] [CharP K 2] [FiniteDimensional K V]

@[expose] noncomputable def omegaInvVec (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) : V :=
  (LinearMap.BilinForm.toDual (polarBilin Q) hQ).symm (omegaInvLambda hs hss)

theorem polar_omegaInvVec_left (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) (x : V) :
    polar Q (omegaInvVec hQ hs hss) x = omegaInvLambda hs hss x := by
  rw [omegaInvVec, ← polarBilin_apply_apply, LinearMap.BilinForm.apply_toDual_symm_apply]

theorem polar_omegaInvVec (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) (x : V) :
    polar Q x (omegaInvVec hQ hs hss) = omegaInvLambda hs hss x := by
  rw [polar_comm, polar_omegaInvVec_left]

theorem eq_omegaInvVec_of_polar (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {v : V}
    (hv : ∀ x, polar Q x v = omegaInvLambda hs hss x) : v = omegaInvVec hQ hs hss := by
  rw [← sub_eq_zero]
  apply eq_zero_of_polar_eq_zero hQ
  intro x
  rw [polar_sub_left, polar_comm Q v x, polar_comm Q _ x, hv, polar_omegaInvVec, sub_self]

theorem omegaInvVec_mem (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) :
    omegaInvVec hQ hs hss ∈ omegaInvSpace s := by
  apply mem_omegaInvSpace_of_forall_polar hQ hs hss
  intro z hz
  rw [polar_omegaInvVec_left, omegaInvLambda_apply, hz, QuadraticMap.map_zero, map_zero]

theorem apply_omegaInvVec_of_commute (hQ : (polarBilin Q).Nondegenerate) {s g : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgs : g * s = s * g) :
    g (omegaInvVec hQ hs hss) = omegaInvVec hQ hs hss := by
  apply eq_omegaInvVec_of_polar hQ hs hss
  intro x
  have hgN : ∀ y, omegaInvNil s (g⁻¹ y) = g⁻¹ (omegaInvNil s y) := by
    intro y
    have hgs' : g⁻¹ * s = s * g⁻¹ := by
      calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * s) * g⁻¹ := by rw [hgs]
        _ = s * g⁻¹ := by group
    rw [omegaInvNil_apply, omegaInvNil_apply, map_sub, ← LinearEquiv.mul_apply, ← hgs',
      LinearEquiv.mul_apply]
  rw [← LinearEquiv.apply_inv_apply' g x, polar_map_of_mem hg, polar_omegaInvVec,
    omegaInvLambda_apply, omegaInvLambda_apply, hgN, map_of_mem (inv_mem hg),
    LinearEquiv.apply_inv_apply']

omit [FiniteDimensional K V] in
theorem omegaInvLambda_of_reduction {s s' : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hs' : s' ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss' : s' * s' = 1) {u w : V}
    (huW : u ∈ omegaInvSpace s) (hwW : w ∈ omegaInvSpace s) (hQu : Q u = 0)
    (hN' : ∀ x, omegaInvNil s' x =
      omegaInvNil s x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u) (x : V) :
    omegaInvLambda hs' hss' x =
      omegaInvLambda hs hss x + polar Q x u * (frobeniusEquiv K 2).symm (Q w) := by
  apply frobenius_inj K 2
  have hfr : ∀ a : K, frobenius K 2 a = a ^ 2 := fun a => rfl
  have hW : ∀ v ∈ omegaInvSpace s, ∀ v' ∈ omegaInvSpace s, polar Q v v' = 0 :=
    fun v hv v' hv' => polar_of_mem_omegaInvSpace hs hss hv hv'
  have hNx := omegaInvNil_mem_omegaInvSpace s x
  rw [hfr, hfr, omegaInvLambda_sq, hN', add_sq, mul_pow, omegaInvLambda_sq,
    show ((frobeniusEquiv K 2).symm (Q w)) ^ 2 = frobenius K 2 ((frobeniusEquiv K 2).symm (Q w))
      from rfl, frobenius_apply_frobeniusEquiv_symm]
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_add Q,
    QuadraticMap.map_smul, QuadraticMap.map_smul, polar_add_left, polar_smul_left,
    polar_smul_right, polar_smul_right, polar_smul_right, hW _ hNx _ hwW, hW _ hNx _ huW,
    hW _ hwW _ huW, hQu]
  simp only [smul_eq_mul, mul_zero, add_zero]
  linear_combination (-(polar Q x u * (frobeniusEquiv K 2).symm (Q w) *
    omegaInvLambda hs hss x)) * h2

theorem map_omegaInvVec (hQ : (polarBilin Q).Nondegenerate) (r : ℕ) :
    ∀ (s : V ≃ₗ[K] V) (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1),
      finrank K (omegaInvSpace s) = r → Q (omegaInvVec hQ hs hss) = (r : K) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s hs hss hr
  have hfr : ∀ a : K, frobenius K 2 a = a ^ 2 := fun a => rfl
  have hsq : Q (omegaInvVec hQ hs hss) = Q (omegaInvVec hQ hs hss) ^ 2 := by
    obtain ⟨y, hy⟩ := mem_omegaInvSpace_iff.1 (omegaInvVec_mem hQ hs hss)
    have h1 : omegaInvLambda hs hss y = Q (omegaInvVec hQ hs hss) := by
      rw [← polar_omegaInvVec hQ hs hss y, ← hy, ← map_omegaInvNil hs]
    calc Q (omegaInvVec hQ hs hss) = Q (omegaInvNil s y) := by rw [hy]
      _ = omegaInvLambda hs hss y ^ 2 := (omegaInvLambda_sq hs hss y).symm
      _ = Q (omegaInvVec hQ hs hss) ^ 2 := by rw [h1]
  by_cases h0 : ∀ x, omegaInvNil s x = 0
  ·
    have hv : (0 : V) = omegaInvVec hQ hs hss := by
      apply eq_omegaInvVec_of_polar hQ hs hss
      intro x
      rw [polar_zero_right, omegaInvLambda_apply, h0, QuadraticMap.map_zero, map_zero]
    have hr0 : r = 0 := by
      rw [← hr, Submodule.finrank_eq_zero]
      rw [eq_bot_iff]
      intro v hv'
      obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 hv'
      rw [h0, Submodule.mem_bot]
    rw [← hv, QuadraticMap.map_zero, hr0, Nat.cast_zero]
  push Not at h0
  obtain ⟨x₁, hx₁⟩ := h0
  have hpos : finrank K (omegaInvSpace s) ≠ 0 := by
    intro h
    rw [Submodule.finrank_eq_zero] at h
    have := omegaInvNil_mem_omegaInvSpace s x₁
    rw [h, Submodule.mem_bot] at this
    exact hx₁ this
  by_cases h1 : finrank K (omegaInvSpace s) = 1
  ·
    rw [← hr, h1, Nat.cast_one]
    have hne : Q (omegaInvVec hQ hs hss) ≠ 0 := by
      intro hQ0
      have hzero : ∀ w ∈ omegaInvSpace s, Q w = 0 := by
        by_cases hx0 : omegaInvVec hQ hs hss = 0
        · intro w hw
          obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 hw
          rw [← omegaInvLambda_sq hs hss, ← polar_omegaInvVec hQ hs hss, hx0, polar_zero_right,
            zero_pow two_ne_zero]
        · have hspan : K ∙ omegaInvVec hQ hs hss = omegaInvSpace s :=
            Submodule.eq_of_le_of_finrank_eq
              ((Submodule.span_singleton_le_iff_mem _ _).2 (omegaInvVec_mem hQ hs hss))
              (by rw [finrank_span_singleton hx0, h1])
          intro w hw
          rw [← hspan] at hw
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
          rw [map_smul_eq_sq, hQ0, mul_zero]
      have hev := even_finrank_commSpace_of_forall_eq_zero hQ hs hss hzero
      rw [← omegaInvSpace_eq_commSpace, h1] at hev
      exact Nat.not_even_one hev
    have e : Q (omegaInvVec hQ hs hss) * (Q (omegaInvVec hQ hs hss) - 1) = 0 := by
      linear_combination -hsq
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hne)
  obtain ⟨u, huW, hu0, hQu⟩ := omegaInv_exists_ne_zero_singular
    (fun v hv w hw => polar_of_mem_omegaInvSpace hs hss hv hw) (by omega)
  obtain ⟨w, hwW, hs'O, hs's', hN', hlt', hpar, -⟩ := exists_eichler_reduction hQ hs hss huW hu0 hQu
  set s' := s * eichler Q u w with hs'
  have hlt : finrank K (omegaInvSpace s') < r := by
    rw [← hr]
    exact Submodule.finrank_lt_finrank_of_lt hlt'
  have hih := ih _ hlt s' hs'O hs's' rfl
  have hvec : omegaInvVec hQ hs hss + (frobeniusEquiv K 2).symm (Q w) • u =
      omegaInvVec hQ hs'O hs's' := by
    apply eq_omegaInvVec_of_polar hQ hs'O hs's'
    intro x
    rw [omegaInvLambda_of_reduction hs hss hs'O hs's' huW hwW hQu hN', polar_add_right,
      polar_omegaInvVec, polar_smul_right_eq, mul_comm]
  have hux : polar Q (omegaInvVec hQ hs hss) u = 0 := by
    rw [polar_omegaInvVec_left, omegaInvLambda_apply, omegaInvNil_of_mem_omegaInvSpace hss huW,
      QuadraticMap.map_zero, map_zero]
  have hQ' : Q (omegaInvVec hQ hs'O hs's') = Q (omegaInvVec hQ hs hss) := by
    rw [← hvec, QuadraticMap.map_add Q, map_smul_eq_sq, hQu, polar_smul_right_eq, hux]
    ring
  rw [← hQ', hih, ← hr]
  exact (CharP.natCast_eq_natCast K 2).2 ((ZMod.natCast_eq_natCast_iff _ _ _).1 hpar)

theorem omegaInvVec_typeB (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V} {l : ℕ}
    (hB : OmegaInvTypeB Q s l) :
    omegaInvVec hQ hB.1 hB.2.1 ∈ omegaInvSpace s ∧ Q (omegaInvVec hQ hB.1 hB.2.1) = 1 ∧
      ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * s = s * g →
        g (omegaInvVec hQ hB.1 hB.2.1) = omegaInvVec hQ hB.1 hB.2.1 ∧
          g * reflect Q (omegaInvVec hQ hB.1 hB.2.1) =
            reflect Q (omegaInvVec hQ hB.1 hB.2.1) * g := by
  obtain ⟨hs, hss, hdim, hodd⟩ := hB
  refine ⟨omegaInvVec_mem hQ hs hss, ?_, fun g hg hgs => ?_⟩
  · rw [map_omegaInvVec hQ _ s hs hss hdim]
    obtain ⟨j, rfl⟩ := hodd
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, omegaInv_two_eq_zero, zero_mul, zero_add,
      Nat.cast_one]
  · have hfix := apply_omegaInvVec_of_commute hQ hs hss hg hgs
    refine ⟨hfix, ?_⟩
    have e := reflect_conj hg (omegaInvVec hQ hs hss)
    rw [hfix] at e
    calc g * reflect Q (omegaInvVec hQ hs hss) =
        (g * reflect Q (omegaInvVec hQ hs hss) * g⁻¹) * g := by group
      _ = reflect Q (omegaInvVec hQ hs hss) * g := by rw [e]

end CFSG.SeitzReduction.SymplecticPilot
