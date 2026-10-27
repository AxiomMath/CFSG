module

public import CFSG.ClassicalInvolution.Asc77.AscT7HS1
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord

public section

namespace CFSG.ClassicalInvolution.Asc77.T7H

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

section Dim

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
theorem minusSp_twinInv_eq (h2 : (2 : F) ≠ 0) (fr : Frame Q) {A A' : SL(2, F)} :
    minusSp (twinInv fr A A') = eigIn (twinInv fr A A') (-1) fr.span := by
  ext x
  constructor
  · intro hx
    rw [mem_minusSp] at hx
    obtain ⟨s, hs, p, hp, rfl⟩ : ∃ s ∈ fr.span, ∃ p ∈ fr.perp, x = s + p :=
      ⟨_, ⟨_, rfl⟩, _, (decomp_span_perp fr x).2, (decomp_span_perp fr x).1⟩
    have hu : twinInv fr A A' (s + p) = twinInv fr A A' s + p := by
      rw [map_add, twinInv_perp fr A A' hp]
    have hmem : twinInv fr A A' s + s ∈ fr.span :=
      fr.span.add_mem (twinInv_mem_span fr hs) hs
    have h1 : twinInv fr A A' s + s = (-2 : F) • p := by
      rw [hu] at hx
      linear_combination (norm := module) hx
    have hp2 : (-2 : F) • p ∈ fr.perp := fr.perp.smul_mem _ hp
    have hm : twinInv fr A A' s + s ∈ fr.span ⊓ fr.perp := ⟨hmem, by rw [h1]; exact hp2⟩
    rw [fr.isCompl_span_perp.inf_eq_bot, Submodule.mem_bot] at hm
    rw [hm] at h1
    have hp0 : p = 0 := by
      rcases smul_eq_zero.mp h1.symm with h | h
      · exact absurd (by linear_combination -h) h2
      · exact h
    subst hp0
    refine ⟨by simpa using hs, ?_⟩
    rw [add_zero, neg_one_smul]
    exact eq_neg_of_add_eq_zero_left hm
  · intro hx
    rw [mem_minusSp, (mem_eigIn_iff.mp hx).2, neg_one_smul]

theorem finrank_minusSp_twinInv (h2 : (2 : F) ≠ 0) (fr : Frame Q) {A A' : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1)
    (hdet : LinearEquiv.det (twinInv fr A A') = 1) :
    Module.finrank F (minusSp (twinInv fr A A')) = 2 := by
  have hii : twinInv fr A A' * twinInv fr A A' = 1 :=
    LinearEquiv.ext fun x => twinInv_twinInv fr hA hA' x
  have heven := even_finrank_minusSp h2 hii hdet
  rw [minusSp_twinInv_eq h2 fr] at heven ⊢
  have hinf : eigIn (twinInv fr A A') (-1) fr.span ⊓ eigIn (twinInv fr A A') 1 fr.span = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2'⟩ := hx
    have e1 := (mem_eigIn_iff.mp h1).2
    have e2 := (mem_eigIn_iff.mp h2').2
    rw [e2, one_smul, neg_one_smul] at e1
    have : (2 : F) • x = 0 := by
      calc (2 : F) • x = x - (-x) := by module
        _ = 0 := by rw [← e1]; exact sub_self _
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.mp this).resolve_left h2
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (eigIn (twinInv fr A A') (-1) fr.span)
    (eigIn (twinInv fr A A') 1 fr.span)
  rw [eig_sup_eq_span fr h2 hA hA', finrank_span_eq_four fr, hinf, finrank_bot] at h4
  have hpos1 : 1 ≤ Module.finrank F (eigIn (twinInv fr A A') (-1) fr.span) :=
    Submodule.one_le_finrank_iff.mpr (eig_ne_bot_neg fr h2 hA hA')
  have hpos2 : 1 ≤ Module.finrank F (eigIn (twinInv fr A A') 1 fr.span) :=
    Submodule.one_le_finrank_iff.mpr (eig_ne_bot_pos fr h2 hA hA')
  obtain ⟨r, hr⟩ := heven
  omega

theorem finrank_plusSp_twinInv (h2 : (2 : F) ≠ 0) (fr : Frame Q) {A A' : SL(2, F)}
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (hA' : (A' : Matrix (Fin 2) (Fin 2) F) * A' = -1)
    (hdet : LinearEquiv.det (twinInv fr A A') = 1) :
    Module.finrank F (plusSp (twinInv fr A A')) = Module.finrank F V - 2 := by
  have hii : twinInv fr A A' * twinInv fr A A' = 1 :=
    LinearEquiv.ext fun x => twinInv_twinInv fr hA hA' x
  have hc := isCompl_plusSp_minusSp h2 hii
  have h := Submodule.finrank_add_eq_of_isCompl hc
  have h2' := finrank_minusSp_twinInv h2 fr hA hA' hdet
  omega

end Dim

section J

variable (F : Type) [Field F]

@[expose] def J2 : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

variable {F}

theorem coe_J2_mul_self :
    ((J2 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (J2 F : Matrix (Fin 2) (Fin 2) F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two]

theorem J2_mul_self : J2 F * J2 F = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_J2_mul_self]
  simp

end J

section Main

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem spin_twin_sq_false (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) [Group.IsPerfect (spinGroup Q)]
    (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F V) (hV4 : ¬ 4 ∣ Module.finrank F V - 2)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ CFSG.ClassicalInvolution.RouteD.Gaps.fundSet Q)
    (hR' : R'.map (spinAction Q) ∈ CFSG.ClassicalInvolution.RouteD.Gaps.fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') (hcomm : ∀ a ∈ R, ∀ b ∈ R', a * b = b * a) {x x' : spinGroup Q} (hx : x ∈ R)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    {c : spinGroup Q} (hc : c ∈ Subgroup.center (spinGroup Q)) (hcc : c * c = x * x') : False := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  set θ := spinAction Q with hθ
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hc
  obtain ⟨w, hw⟩ : ∃ w : V, Q w ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (eq_zero_of_polar_eq_zero hQ fun y => by
      rw [polar, hall, hall, hall]; simp)
  have hμ2 : μ * μ = 1 := by
    have h1 := map_spinAction Q c w
    rw [hμ w, QuadraticMap.map_smul, smul_eq_mul] at h1
    exact mul_right_cancel₀ hw (by rw [one_mul]; exact h1)
  have hθcc : θ c * θ c = 1 := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, hμ v, map_smul, hμ v, smul_smul, hμ2, one_smul]
    rfl
  have hxx' : θ x * θ x' = 1 := by
    rw [← map_mul, ← hcc, map_mul]
    exact hθcc
  have hx'sq : θ x' * θ x' = 1 := by rw [← map_mul, hx'2, map_one]
  have hord : θ x = θ x' := mul_right_cancel (hxx'.trans hx'sq.symm)
  obtain ⟨F₁, hF₁, hF₁', hθx, hθx'⟩ :=
    CFSG.ClassicalInvolution.G2D4Models.Twin.swap_of_twin_pair_ord hodd hRp hR'p hR hR' hinj hinj'
      hne hx hx2 hx1 hx' hx'2 hx'1 hord
  obtain ⟨a, haR, hθa⟩ : ∃ a ∈ R, θ a = F₁.La (J2 F) := by
    have : F₁.La (J2 F) ∈ R.map θ := by rw [hF₁]; exact ⟨J2 F, rfl⟩
    obtain ⟨a, ha, h⟩ := this
    exact ⟨a, ha, h⟩
  obtain ⟨a', ha'R, hθa'⟩ : ∃ a' ∈ R', θ a' = F₁.swap.La (J2 F) := by
    have : F₁.swap.La (J2 F) ∈ R'.map θ := by rw [hF₁']; exact ⟨J2 F, rfl⟩
    obtain ⟨a', ha', h⟩ := this
    exact ⟨a', ha', h⟩
  have haa : a * a = x := by
    have h1 : θ (a * a * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hθa, hθx, ← map_mul, J2_mul_self]
      exact mul_inv_cancel _
    have := hinj (a * a * x⁻¹) (R.mul_mem (R.mul_mem haR haR) (R.inv_mem hx)) h1
    rwa [mul_inv_eq_one] at this
  have ha'a' : a' * a' = x' := by
    have h1 : θ (a' * a' * x'⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hθa', hθx', ← map_mul, J2_mul_self]
      exact mul_inv_cancel _
    have := hinj' (a' * a' * x'⁻¹) (R'.mul_mem (R'.mul_mem ha'R ha'R) (R'.inv_mem hx')) h1
    rwa [mul_inv_eq_one] at this
  have hcomm' : a' * a = a * a' := (hcomm a haR a' ha'R).symm
  have huu : a * a' * (a * a') = x * x' := by
    calc a * a' * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [hcomm']
      _ = (a * a) * (a' * a') := by group
      _ = x * x' := by rw [haa, ha'a']
  have hcinv : c⁻¹ ∈ Subgroup.center (spinGroup Q) := inv_mem hc
  have hvv : (a * a' * c⁻¹) * (a * a' * c⁻¹) = 1 := by
    calc a * a' * c⁻¹ * (a * a' * c⁻¹) = a * a' * (c⁻¹ * (a * a')) * c⁻¹ := by group
      _ = a * a' * ((a * a') * c⁻¹) * c⁻¹ := by
          rw [← Subgroup.mem_center_iff.mp hcinv (a * a')]
      _ = (a * a' * (a * a')) * (c⁻¹ * c⁻¹) := by group
      _ = 1 := by rw [huu, ← hcc]; group
  have h4 := four_dvd_finrank_minusSp_of_sq_one h2 hQ hvv (det_spinAction_eq_one _)
  have hAA : ((J2 F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (J2 F : Matrix (Fin 2) (Fin 2) F) =
      -1 := coe_J2_mul_self
  have hdetu : LinearEquiv.det (twinInv F₁ (J2 F) (J2 F)) = 1 := by
    have := det_spinAction_eq_one (a * a')
    rwa [map_mul, hθa, hθa'] at this
  have hθv : θ (a * a' * c⁻¹) = twinInv F₁ (J2 F) (J2 F) * (θ c)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hθa, hθa']
    rfl
  rcases mul_self_eq_one_iff.mp hμ2 with h | h
  · have hθc : θ c = 1 := LinearEquiv.ext fun v => by rw [hμ v, h, one_smul]; rfl
    rw [hθv, hθc, inv_one, mul_one, finrank_minusSp_twinInv h2 F₁ hAA hAA hdetu] at h4
    omega
  · have hθc : θ c = LinearEquiv.neg F := LinearEquiv.ext fun v => by
      rw [hμ v, h, neg_one_smul]; rfl
    have hneg : (LinearEquiv.neg F : V ≃ₗ[F] V)⁻¹ = LinearEquiv.neg F := by
      refine inv_eq_of_mul_eq_one_right (LinearEquiv.ext fun v => ?_)
      simp
    have hms : minusSp (twinInv F₁ (J2 F) (J2 F) * LinearEquiv.neg F) =
        plusSp (twinInv F₁ (J2 F) (J2 F)) := by
      ext v
      rw [mem_minusSp, mem_plusSp, LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg, neg_inj]
    rw [hθv, hθc, hneg, hms, finrank_plusSp_twinInv h2 F₁ hAA hAA hdetu] at h4
    exact hV4 h4

end Main

end CFSG.ClassicalInvolution.Asc77.T7H
