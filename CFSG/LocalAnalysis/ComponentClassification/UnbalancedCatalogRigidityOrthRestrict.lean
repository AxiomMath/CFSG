module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthQuotient
public import CFSG.ClassicalGroups.Alternating.Generation

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (mem_matrixDerived_iff)
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply
  symplecticTransvection_zero alternating_transvection_generation)

variable {K : Type} [Field K] {d : ℕ}

abbrev symmetryCentralizer (Q : QuadraticForm K (Fin d → K)) (v : Fin d → K) :
    Subgroup (GL (Fin d) K) :=
  matrixIsometries Q ⊓ Subgroup.centralizer {symmetryGL Q v}

variable {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K}

theorem symmetryGL_mem_symmetryCentralizer : symmetryGL Q v ∈ symmetryCentralizer Q v :=
  ⟨symmetryGL_mem Q v, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem polar_mulVec_of_mem {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) (x y : Fin d → K) :
    polar Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ x) ((g : Matrix (Fin d) (Fin d) K) *ᵥ y) =
      polar Q x y :=
  polar_map_of_mem (show matrixLinearIso g ∈ TauCeti.QuadraticMap.orthogonalGroup Q from hg) x y

theorem map_mulVec_of_mem {g : GL (Fin d) K} (hg : g ∈ matrixIsometries Q) (x : Fin d → K) :
    Q ((g : Matrix (Fin d) (Fin d) K) *ᵥ x) = Q x :=
  (mem_matrixIsometries_iff Q g).mp hg x

section Restrict

variable [CharP K 2] (hQ : Q.polarBilin.Nondegenerate) (hv : Q v = 1)
include hQ hv

theorem fix_of_mem_symmetryCentralizer {g : GL (Fin d) K} (hg : g ∈ symmetryCentralizer Q v) :
    (g : Matrix (Fin d) (Fin d) K) *ᵥ v = v :=
  (mem_centralizer_symmetryGL_iff hQ hv hg.1).mp hg.2

@[expose] def symmetryRestrict :
    symmetryCentralizer Q v →* LinearMap.GeneralLinearGroup K (vQuot Q v) where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (quotEquivOfFix (e := matrixLinearEquiv g.1) (fix_of_mem_symmetryCentralizer hQ hv g.2)
      (polar_mulVec_of_mem g.2.1))
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (Matrix.one_mulVec _))
  map_mul' g h := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      change (((g * h : symmetryCentralizer Q v) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          (x : Fin d → K) = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
            (((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K))
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem symmetryRestrict_mk (g : symmetryCentralizer Q v) (x : vPerp Q v) :
    ((symmetryRestrict hQ hv g : LinearMap.GeneralLinearGroup K (vQuot Q v)) :
      vQuot Q v →ₗ[K] vQuot Q v) (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk (perpEquivOfFix (e := matrixLinearEquiv g.1)
          (fix_of_mem_symmetryCentralizer hQ hv g.2) (polar_mulVec_of_mem g.2.1) x) := rfl

theorem symmetryRestrict_mem (g : symmetryCentralizer Q v) :
    symmetryRestrict hQ hv g ∈ bilinIsometryGroup (vQuotForm Q v) := by
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [symmetryRestrict_mk, symmetryRestrict_mk, vQuotForm_mk, vQuotForm_mk]
      exact polar_mulVec_of_mem g.2.1 x y

theorem eq_one_or_eq_symmetryGL_of_restrict_eq_one {g : symmetryCentralizer Q v}
    (hg : symmetryRestrict hQ hv g = 1) :
    (g : GL (Fin d) K) = 1 ∨ (g : GL (Fin d) K) = symmetryGL Q v := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hgv := fix_of_mem_symmetryCentralizer hQ hv g.2
  have hgO := g.2.1
  have hperp : ∀ x ∈ vPerp Q v, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x = x := by
    intro x hx
    have h1 := congrArg (fun φ : LinearMap.GeneralLinearGroup K (vQuot Q v) =>
      (φ : vQuot Q v →ₗ[K] vQuot Q v) (Submodule.Quotient.mk ⟨x, hx⟩)) hg
    simp only [symmetryRestrict_mk, Units.val_one, Module.End.one_apply] at h1
    rw [Submodule.Quotient.eq] at h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    have hc' : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x = x + c • v := by
      have : c • v = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ x - x := hc
      rw [this]
      abel
    have hQx := map_mulVec_of_mem hgO x
    rw [hc', QuadraticMap.map_add Q, QuadraticMap.map_smul, hv, smul_eq_mul, mul_one,
      polar_smul_right, smul_eq_mul, polar_comm, (mem_vPerp Q v).mp hx, mul_zero,
      add_zero] at hQx
    have hc0 : c ^ 2 = 0 := by linear_combination hQx
    rw [hc', (pow_eq_zero_iff two_ne_zero).mp hc0, zero_smul, add_zero]
  obtain ⟨w, hw⟩ := exists_polar_eq_one hQ hv0
  set c := polar Q (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) w - polar Q w w
    with hc
  have hgw : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w = w + c • v := by
    have hz : ∀ u, polar Q (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w - w - c • v)
        u = 0 := by
      intro u
      have hu' := sub_smul_mem_vPerp hw u
      have h1 : polar Q (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w)
          (u - polar Q v u • w) = polar Q w (u - polar Q v u • w) := by
        rw [← polar_mulVec_of_mem hgO w (u - polar Q v u • w), hperp _ hu']
      have h2 : polar Q v (u - polar Q v u • w) = 0 := hu'
      simp only [polar_sub_left, polar_sub_right, polar_smul_left, polar_smul_right,
        smul_eq_mul] at h1 h2 ⊢
      linear_combination h1 - polar Q v u * hc
    have hz0 := hQ.1 _ fun u => by rw [QuadraticMap.polarBilin_apply_apply]; exact hz u
    rw [sub_eq_zero, sub_eq_iff_eq_add] at hz0
    rw [hz0]
    abel
  have hc2 : c * c + c = 0 := by
    have hQw := map_mulVec_of_mem hgO w
    rw [hgw, QuadraticMap.map_add Q, QuadraticMap.map_smul, hv, smul_eq_mul, mul_one,
      polar_smul_right, smul_eq_mul, polar_comm, hw, mul_one] at hQw
    linear_combination hQw
  have hc01 : c = 0 ∨ c = 1 := by
    have h1 : c * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h - h22)
  have hdec : ∀ u : Fin d → K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u =
      u + (c * polar Q v u) • v := by
    intro u
    have hu := hperp _ (sub_smul_mem_vPerp hw u)
    calc ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u
        _ = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
            ((u - polar Q v u • w) + polar Q v u • w) := by rw [sub_add_cancel]
        _ = (u - polar Q v u • w) + polar Q v u • (w + c • v) := by
          rw [mulVec_add, mulVec_smul, hu, hgw]
        _ = u + (c * polar Q v u) • v := by module
  rcases hc01 with h0 | h1
  · left
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro u
    rw [hdec, h0, zero_mul, zero_smul, add_zero, Units.val_one, one_mulVec]
  · right
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro u
    rw [hdec, h1, one_mul, symmetryGL_mulVec_of_charTwo hv]

theorem ker_symmetryRestrict :
    (symmetryRestrict hQ hv).ker =
      Subgroup.zpowers ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ := by
  apply le_antisymm
  · intro g hg
    rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv hg with h | h
    · have hg1 : g = 1 := Subtype.ext h
      rw [hg1]
      exact one_mem _
    · have hgs : g = ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ := Subtype.ext h
      rw [hgs]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    apply Units.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      change ((symmetryGL Q v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K) = x
      rw [symmetryGL_mulVec_of_charTwo hv, (mem_vPerp Q v).mp x.2, zero_smul, add_zero]

end Restrict

theorem reflect_mul_reflect_eq_eichler {V : Type*} [AddCommGroup V] [Module K V] [CharP K 2]
    {Q : QuadraticForm K V} {z v : V} (hz : Q z = 1) (hv : Q v = 1) (hzv : polar Q z v = 0) :
    reflect Q z * reflect Q v = eichler Q (z + v) z := by
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hzz : polar Q z z = 0 := by rw [polar_self, hz, two_nsmul, CharTwo.add_self_eq_zero]
  have hu : Q (z + v) = 0 := by
    rw [QuadraticMap.map_add Q, hz, hv, hzv, add_zero]
    linear_combination h22
  have huw : polar Q (z + v) z = 0 := by rw [polar_add_left, hzz, polar_comm, hzv, add_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, reflect_apply (by rw [hz]; exact one_ne_zero),
    reflect_apply (by rw [hv]; exact one_ne_zero), eichler_apply hu huw, hz, hv]
  simp only [div_one, polar_sub_right, polar_smul_right, polar_add_right, smul_eq_mul, one_mul]
  simp only [hzv, mul_zero, sub_zero]
  rw [polar_comm Q x z, polar_comm Q x v,
    show polar Q z x + (polar Q z x + polar Q v x) = polar Q v x + (polar Q z x + polar Q z x)
      by ring, CharTwo.add_self_eq_zero, add_zero]
  simp only [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  have h2z : (2 : K) • z = 0 := by rw [h22, zero_smul]
  linear_combination (norm := module) (-polar Q v x) • h2z

section Lift

variable [CharP K 2] [Finite K] (hQ : Q.polarBilin.Nondegenerate) (hv : Q v = 1)
include hQ hv

theorem exists_lift_transvection
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) (u : vPerp Q v) (c : K) :
    ∃ g : symmetryCentralizer Q v, (g : GL (Fin d) K) ∈ matrixDerived Q ∧
      symmetryRestrict hQ hv g = symplecticTransvection (vQuotForm Q v) (vQuotForm_isAlt Q v)
        (Submodule.Quotient.mk u) c := by
  by_cases hc : c = 0
  · refine ⟨1, one_mem _, ?_⟩
    rw [map_one, hc, symplecticTransvection_zero]
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c⁻¹ + Q u)
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have huv : polar Q (u : Fin d → K) v = 0 := by
    rw [polar_comm]
    exact u.2
  have hvv : polar Q v v = 0 := by rw [polar_self, hv, two_nsmul, CharTwo.add_self_eq_zero]
  set z₀ : Fin d → K := (u : Fin d → K) + b • v with hz₀def
  set z : Fin d → K := l • z₀ with hzdef
  have hz₀ : Q z₀ = c⁻¹ := by
    rw [hz₀def, QuadraticMap.map_add Q, QuadraticMap.map_smul, hv, polar_smul_right, huv,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_one]
    linear_combination hb.symm + Q u * h22
  have hz : Q z = 1 := by
    rw [hzdef, QuadraticMap.map_smul, hz₀, smul_eq_mul, ← hl, mul_inv_cancel₀ hc]
  have hzv : polar Q z v = 0 := by
    rw [hzdef, hz₀def, polar_smul_left, polar_add_left, polar_smul_left, huv, hvv, smul_zero,
      add_zero, smul_zero]
  have hsz : symmetryGL Q z ∈ symmetryCentralizer Q v := by
    refine ⟨symmetryGL_mem Q z, (mem_centralizer_symmetryGL_iff hQ hv (symmetryGL_mem Q z)).mpr ?_⟩
    rw [symmetryGL_mulVec_of_charTwo hz, hzv, zero_smul, add_zero]
  refine ⟨⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩, ?_, ?_⟩
  · rw [mem_matrixDerived_iff, Subgroup.coe_mul, map_mul, matrixLinearIso_symmetryGL,
      matrixLinearIso_symmetryGL, reflect_mul_reflect_eq_eichler hz hv hzv, hE]
    exact eichler_mem_elementaryGroup Q _ _
  · apply Units.ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [symmetryRestrict_mk, symplecticTransvection_apply, vQuotForm_mk,
        ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
        Submodule.mem_comap]
      have hx : polar Q v (x : Fin d → K) = 0 := x.2
      have hxz₀ : polar Q z₀ (x : Fin d → K) = polar Q (x : Fin d → K) u := by
        rw [hz₀def, polar_add_left, polar_smul_left, hx, smul_zero, add_zero, polar_comm]
      have hact : ((((⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v,
          symmetryGL_mem_symmetryCentralizer⟩ : symmetryCentralizer Q v) : GL (Fin d) K) :
            Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K)) =
          (x : Fin d → K) + (c * polar Q (x : Fin d → K) u) • (u : Fin d → K) +
            (c * polar Q (x : Fin d → K) u * b) • v := by
        rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, symmetryGL_mulVec_of_charTwo hv,
          hx, zero_smul, add_zero, symmetryGL_mulVec_of_charTwo hz, hzdef, polar_smul_left,
          hxz₀, hl, hz₀def]
        module
      refine Submodule.mem_span_singleton.mpr ⟨c * polar Q (x : Fin d → K) u * b, ?_⟩
      simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_add,
        Submodule.coe_smul]
      change _ = ((((⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v,
          symmetryGL_mem_symmetryCentralizer⟩ : symmetryCentralizer Q v) : GL (Fin d) K) :
            Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K)) - _
      rw [hact]
      abel

theorem map_derived_symmetryRestrict
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    ((matrixDerived Q ⊓ symmetryCentralizer Q v).subgroupOf (symmetryCentralizer Q v)).map
      (symmetryRestrict hQ hv) = bilinIsometryGroup (vQuotForm Q v) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  apply le_antisymm
  · rintro _ ⟨g, -, rfl⟩
    exact symmetryRestrict_mem hQ hv g
  · rw [alternating_transvection_generation (vQuotForm_isAlt Q v)
      (vQuotForm_nondegenerate hQ hv0), Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨g, hgH, hg⟩ := exists_lift_transvection hQ hv hE u c
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨hgH, g.2⟩, hg⟩

theorem range_symmetryRestrict
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    (symmetryRestrict hQ hv).range = bilinIsometryGroup (vQuotForm Q v) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact symmetryRestrict_mem hQ hv g
  · rw [← map_derived_symmetryRestrict hQ hv hE]
    exact Subgroup.map_le_range _ _

end Lift

end CFSG.ComponentClassification.UnbalancedCatalog
