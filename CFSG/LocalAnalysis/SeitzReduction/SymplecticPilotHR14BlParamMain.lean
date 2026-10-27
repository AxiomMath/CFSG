module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordFixed
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlParamNormal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviSympChart

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup QuadraticMap Module Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.PartOne.AUTSL (reflMat reflMat_mem_isometries reflMat_mul_self comm_reflMat_iff
  mul_reflMat_mem_iff reflMat_mulVec_one reflMat_not_mem_derived mem_matrixDerived_iff_even)
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)

section Model

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem bParam_symmetryGL_eq_reflMat [CharP K 2] {w : Fin d → K} (hw : Q w = 1)
    (hw0 : Q w ≠ 0) : symmetryGL Q w = reflMat Q w hw0 := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [symmetryGL_mulVec_of_charTwo hw, reflMat_mulVec_one w hw hw0]

theorem bParam_finrank_vPerp (hQ : Q.polarBilin.Nondegenerate) {w : Fin d → K} (hw0 : w ≠ 0) :
    1 + finrank K (vPerp Q w) = d := by
  obtain ⟨w', hw'⟩ := exists_polar_eq_one hQ hw0
  have h1 := LinearMap.finrank_range_add_finrank_ker (Q.polarBilin w)
  have hrange : LinearMap.range (Q.polarBilin w) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    refine ⟨c • w', ?_⟩
    rw [map_smul, QuadraticMap.polarBilin_apply_apply, hw', smul_eq_mul, mul_one]
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  exact h1

theorem bParam_typeA [CharP K 2] {w : Fin d → K} {S : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hS : S ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hW1 : ∀ u, polar Q u w ^ 2 = Q (omegaInvNil S u)) (y : vQuot Q w →ₗ[K] vQuot Q w)
    (hy : ∀ u : vPerp Q w, ∃ hu : S u ∈ vPerp Q w,
      y (Submodule.Quotient.mk u) = Submodule.Quotient.mk ⟨S u, hu⟩) (u : vQuot Q w) :
    vQuotForm Q w u (y u) = 0 := by
  induction u using Submodule.Quotient.induction_on with
  | H u =>
    obtain ⟨hu, hyu⟩ := hy u
    rw [hyu, vQuotForm_mk]
    change polar Q (u : Fin d → K) (S u) = 0
    have hSu : S u = (u : Fin d → K) + omegaInvNil S u := by
      rw [omegaInvNil_apply]
      abel
    have hpu : polar Q (u : Fin d → K) w = 0 := by
      rw [polar_comm]
      exact u.2
    rw [hSu, polar_add_right, polar_self, two_nsmul, CharTwo.add_self_eq_zero, zero_add,
      ← map_omegaInvNil hS, ← hW1, hpu, zero_pow two_ne_zero]

theorem bParam_finrank_range [CharP K 2] (hQ : Q.polarBilin.Nondegenerate) {w : Fin d → K}
    (hw : Q w = 1) {S : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hW1 : ∀ u, polar Q u w ^ 2 = Q (omegaInvNil S u)) {j : ℕ}
    (hrank : finrank K (LinearMap.range (omegaInvNil S)) = 2 * j + 1)
    (y : vQuot Q w →ₗ[K] vQuot Q w)
    (hy : ∀ u : vPerp Q w, ∃ hu : S u ∈ vPerp Q w,
      y (Submodule.Quotient.mk u) = Submodule.Quotient.mk ⟨S u, hu⟩) :
    finrank K (LinearMap.range (y - LinearMap.id : vQuot Q w →ₗ[K] vQuot Q w)) = 2 * j := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hw
    exact zero_ne_one hw
  set ψ : vPerp Q w →ₗ[K] vQuot Q w :=
    (y - LinearMap.id : vQuot Q w →ₗ[K] vQuot Q w) ∘ₗ (vLine Q w).mkQ with hψ
  have hrange : LinearMap.range ψ =
      LinearMap.range (y - LinearMap.id : vQuot Q w →ₗ[K] vQuot Q w) :=
    LinearMap.range_comp_of_range_eq_top _ (Submodule.range_mkQ _)
  have hker : ∀ u : vPerp Q w, u ∈ LinearMap.ker ψ ↔ omegaInvNil S u = 0 := by
    intro u
    obtain ⟨hu, hyu⟩ := hy u
    rw [LinearMap.mem_ker, hψ, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply,
      LinearMap.id_apply, hyu, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      have hNu : omegaInvNil S u = a • w := by
        rw [omegaInvNil_apply, ha]
      have h1 := hW1 u
      have hpu : polar Q (u : Fin d → K) w = 0 := by
        rw [polar_comm]
        exact u.2
      rw [hNu, CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hw, mul_one, hpu,
        zero_pow two_ne_zero] at h1
      have ha0 : a = 0 := (pow_eq_zero_iff two_ne_zero).1 h1.symm
      rw [hNu, ha0, zero_smul]
    · intro h
      refine ⟨0, ?_⟩
      rw [zero_smul]
      change (0 : Fin d → K) = S u - u
      rw [← omegaInvNil_apply, h]
  have hkerN : LinearMap.ker (omegaInvNil S) ≤ vPerp Q w := by
    intro u hu
    rw [LinearMap.mem_ker] at hu
    rw [mem_vPerp, polar_comm]
    have h1 := hW1 u
    rw [hu, QuadraticMap.map_zero] at h1
    exact (pow_eq_zero_iff two_ne_zero).1 h1
  have hkerψ : LinearMap.ker ψ = (LinearMap.ker (omegaInvNil S)).comap (vPerp Q w).subtype := by
    ext u
    rw [hker u, Submodule.mem_comap, LinearMap.mem_ker, Submodule.subtype_apply]
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hrange, hkerψ, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hkerN)] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (omegaInvNil S)
  rw [hrank, Module.finrank_fin_fun] at h2
  have h3 := bParam_finrank_vPerp hQ hw0
  omega

end Model

theorem bParam_polar_sq {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {Q : QuadraticForm K (Fin (2 * (n + 1)) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * (n + 1)) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : matrixIsometries Q} (hs : s * s = 1) {j : ℕ} (hj : 1 ≤ j)
    (hrank : finrank K (commSpace (matrixLinearIso s.val)) = 2 * j + 1)
    {w : Fin (2 * (n + 1)) → K} (hw : Q w = 1)
    (hfixw : ∀ g : GL (Fin (2 * (n + 1))) K, g ∈ matrixIsometries Q → g * s.val = s.val * g →
      (g : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ w = w)
    (u : Fin (2 * (n + 1)) → K) :
    polar Q u w ^ 2 = Q (omegaInvNil (matrixLinearIso s.val) u) := by
  have hS : matrixLinearIso s.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have hSS := bCoord_mul_self_linear hs
  have hB : OmegaInvTypeB Q (matrixLinearIso s.val)
      (finrank K (omegaInvSpace (matrixLinearIso s.val))) := ⟨hS, hSS, rfl, by
        change Odd (finrank K (commSpace (matrixLinearIso s.val)))
        rw [hrank]
        exact ⟨j, rfl⟩⟩
  obtain ⟨hmem, hQx, -⟩ := omegaInvVec_typeB hQ hB
  have hxs : omegaInvVec hQ hB.1 hB.2.1 ∈ K ∙ w := by
    refine omegaBFixedVectorInput_holds n K Q hQ hT hE s hs j hj hrank w hw hfixw _
      (apply_of_mem_omegaInvSpace hSS hmem) fun g hg hgs => ?_
    refine apply_omegaInvVec_of_commute hQ hB.1 hB.2.1 (matrixDerived_le_isometries Q hg) ?_
    change matrixLinearIso g * matrixLinearIso s.val = matrixLinearIso s.val * matrixLinearIso g
    rw [← map_mul, ← map_mul, hgs]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hxs
  have hc1 : c = 1 := by
    have h3 := congrArg Q hc
    rw [CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq, hw, mul_one, hQx, _root_.sq] at h3
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.eq_one_of_mul_self_eq_one_of_charTwo h3
  have hxw : omegaInvVec hQ hB.1 hB.2.1 = w := by rw [← hc, hc1, one_smul]
  rw [← hxw, polar_omegaInvVec, omegaInvLambda_sq]

theorem omegaBSpParamInput_holds : OmegaBSpParamInput := by
  intro n K _ _ _ Q hQ hT hE s hs j hj hrank w hw0 hw hfixw
  have hwne : w ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hw
    exact zero_ne_one hw
  have hW1 := bParam_polar_sq hQ hT hE hs hj hrank hw hfixw
  have hsym := bParam_symmetryGL_eq_reflMat hw hw0
  set r := reflMat Q w hw0 with hr
  have hsw : (s.val : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ w = w :=
    hfixw s.val s.2 rfl
  have hsr : s.val * r = r * s.val := (comm_reflMat_iff hQ s.2 hw hw0).2 hsw
  have hrr : r * r = 1 := reflMat_mul_self w hw0
  have hss : s.val * s.val = 1 := congrArg Subtype.val hs
  set x₀ : GL (Fin (2 * (n + 1))) K := s.val * r with hx₀
  have hsΩ : s.val ∉ matrixDerived Q := by
    rw [mem_matrixDerived_iff_even hQ hT s.2, hrank]
    rintro ⟨k, hk⟩
    omega
  have hx₀Ω : x₀ ∈ matrixDerived Q := (mul_reflMat_mem_iff hQ hT s.2 w hw0).2 hsΩ
  have hx₀O : x₀ ∈ matrixIsometries Q := mul_mem s.2 (reflMat_mem_isometries w hw0)
  have hx₀r : x₀ * r = r * x₀ := by
    rw [hx₀, ← mul_assoc r, ← hsr]
  have hx₀x₀ : x₀ * x₀ = 1 := by
    calc x₀ * x₀ = s.val * (r * s.val) * r := by rw [hx₀]; group
      _ = 1 := by rw [← hsr, ← mul_assoc, hss, one_mul, hrr]
  set H : Subgroup (GL (Fin (2 * (n + 1))) K) := matrixDerived Q ⊓ symmetryCentralizer Q w
    with hH
  have hHC : H ≤ symmetryCentralizer Q w := inf_le_right
  have hx₀C : x₀ ∈ centralizer {symmetryGL Q w} := by
    rw [mem_centralizer_singleton_iff, hsym]
    exact hx₀r
  have hx₀H : x₀ ∈ H := ⟨hx₀Ω, hx₀O, hx₀C⟩
  set ρ : H →* Module.End K (vQuot Q w) :=
    (Units.coeHom (Module.End K (vQuot Q w))).comp
      ((symmetryRestrict hQ hw).comp (Subgroup.inclusion hHC)) with hρ
  have hρiso : ∀ g u u', vQuotForm Q w (ρ g u) (ρ g u') = vQuotForm Q w u u' :=
    fun g u u' => symmetryRestrict_mem hQ hw (Subgroup.inclusion hHC g) u u'
  set y : Module.End K (vQuot Q w) := ρ ⟨x₀, hx₀H⟩ with hy
  have hyact : ∀ u : vPerp Q w, ∃ hu : matrixLinearIso s.val u ∈ vPerp Q w,
      y (Submodule.Quotient.mk u) = Submodule.Quotient.mk ⟨matrixLinearIso s.val u, hu⟩ := by
    intro u
    have hx₀u : (x₀ : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) K) *ᵥ (u : Fin _ → K) =
        matrixLinearIso s.val u := by
      rw [hx₀, Units.val_mul, ← Matrix.mulVec_mulVec, reflMat_mulVec_one w hw hw0,
        (mem_vPerp Q w).1 u.2, zero_smul, add_zero]
      rfl
    have hmem : matrixLinearIso s.val u ∈ vPerp Q w := by
      rw [← hx₀u]
      exact (perpEquivOfFix (e := matrixLinearEquiv x₀)
        (fix_of_mem_symmetryCentralizer hQ hw (hHC hx₀H)) (polar_mulVec_of_mem hx₀O) u).2
    refine ⟨hmem, ?_⟩
    change Submodule.Quotient.mk (perpEquivOfFix (e := matrixLinearEquiv x₀)
      (fix_of_mem_symmetryCentralizer hQ hw (hHC hx₀H)) (polar_mulVec_of_mem hx₀O) u) = _
    congr 1
    exact Subtype.ext hx₀u
  have hU : finrank K (vQuot Q w) = 2 * n := by
    have := finrank_vQuot hQ hw
    omega
  have hyy : ∀ u, y (y u) = u := by
    intro u
    have h1 : (⟨x₀, hx₀H⟩ : H) * ⟨x₀, hx₀H⟩ = 1 := Subtype.ext hx₀x₀
    have h2 := congrArg (fun g => ρ g u) h1
    simp only [map_mul, map_one, Module.End.mul_apply, Module.End.one_apply] at h2
    exact h2
  have ha := bParam_typeA (S := matrixLinearIso s.val) s.2 hW1 y hyact
  have hrank' : finrank K (LinearMap.range (omegaInvNil (matrixLinearIso s.val))) = 2 * j + 1 := by
    have h := hrank
    rw [← omegaInvSpace_eq_commSpace] at h
    exact h
  have hrk := bParam_finrank_range hQ hw hW1 hrank' y hyact
  obtain ⟨b, hb, hbmat⟩ := exists_isSymplecticBasis_toMatrix_eq_spARep (vQuotForm_isAlt Q w)
    (vQuotForm_nondegenerate hQ hwne) hU (hρiso _) hyy ha hrk
  set χ₀ : H →* StatedSp n K :=
    CFSG.SeitzReduction.OmegaPilot.sympChart (vQuotForm_isAlt Q w) hb ρ hρiso with hχ₀
  have hχinj : Function.Injective χ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hχ₀, CFSG.SeitzReduction.OmegaPilot.sympChart_ker,
      eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hg' : symmetryRestrict hQ hw (Subgroup.inclusion hHC g) = 1 := Units.ext hg
    rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hw hg' with h | h
    · exact (Subgroup.mem_bot).2 (Subtype.ext h)
    · exfalso
      have hgΩ : (g : GL (Fin (2 * (n + 1))) K) ∈ matrixDerived Q := g.2.1
      have h' : (g : GL (Fin (2 * (n + 1))) K) = r := h.trans hsym
      rw [h'] at hgΩ
      exact reflMat_not_mem_derived hQ hT w hw0 hgΩ
  have hχsurj : Function.Surjective χ₀ := by
    apply CFSG.SeitzReduction.OmegaPilot.sympChart_surjective
    intro f hf
    have hfinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro u hu
      rw [LinearMap.mem_ker] at hu
      rw [Submodule.mem_bot]
      apply (vQuotForm_nondegenerate hQ hwne).1
      intro u'
      rw [← hf, hu, map_zero, LinearMap.zero_apply]
    set F := LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofInjectiveEndo f hfinj)
      with hF
    have hFf : (F : vQuot Q w →ₗ[K] vQuot Q w) = f := LinearMap.ext fun _ => rfl
    have hFmem : F ∈ CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (vQuotForm Q w) := by
      intro u u'
      rw [hFf]
      exact hf u u'
    rw [← map_derived_symmetryRestrict hQ hw hE] at hFmem
    obtain ⟨g, hgH, hgF⟩ := hFmem
    have hgH' : (g : GL (Fin (2 * (n + 1))) K) ∈ H := Subgroup.mem_subgroupOf.1 hgH
    refine ⟨⟨g, hgH'⟩, ?_⟩
    change ((symmetryRestrict hQ hw g : LinearMap.GeneralLinearGroup K (vQuot Q w)) :
      vQuot Q w →ₗ[K] vQuot Q w) = f
    rw [hgF, hFf]
  set χ : H ≃* StatedSp n K := MulEquiv.ofBijective χ₀ ⟨hχinj, hχsurj⟩ with hχ
  have hχx₀ : χ ⟨x₀, hx₀H⟩ = spARep n j := by
    apply Subtype.ext
    apply Units.ext
    change LinearMap.toMatrix b b y = _
    rw [hbmat, spARep, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.coe_upperUnipotentSp]
  refine ⟨H.subtype.comp χ.symm.toMonoidHom, Subtype.val_injective.comp χ.symm.injective,
    fun x => ?_, fun g hg hgr => ?_, ?_⟩
  · obtain ⟨hΩ, -, hc⟩ := (χ.symm x).2
    refine ⟨hΩ, ?_⟩
    have h1 := mem_centralizer_singleton_iff.1 hc
    rw [hsym] at h1
    exact h1
  · have hgC : g ∈ centralizer {symmetryGL Q w} := by
      rw [mem_centralizer_singleton_iff, hsym]
      exact hgr
    have hgH : g ∈ H := ⟨hg, matrixDerived_le_isometries Q hg, hgC⟩
    refine ⟨χ ⟨g, hgH⟩, ?_⟩
    change ((χ.symm (χ ⟨g, hgH⟩) : H) : GL (Fin (2 * (n + 1))) K) = g
    rw [MulEquiv.symm_apply_apply]
  · change ((χ.symm (spARep n j) : H) : GL (Fin (2 * (n + 1))) K) = s.val * r
    rw [← hχx₀, MulEquiv.symm_apply_apply]

end CFSG.SeitzReduction.SymplecticPilot
