module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2

section SemiConj

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K ≃+* K} {F : V ≃+ V}

theorem symm_smul_of_semilinear (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (c : K)
    (v : V) : F.symm (c • v) = σ.symm c • F.symm v := by
  apply F.injective
  rw [AddEquiv.apply_symm_apply, hF, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

@[expose] def semiConj (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (g : V ≃ₗ[K] V) :
    V ≃ₗ[K] V :=
  (F.symm.trans (g.toAddEquiv.trans F)).toLinearEquiv fun c v => by
    change F (g (F.symm (c • v))) = c • F (g (F.symm v))
    rw [symm_smul_of_semilinear hF, map_smul, hF, RingEquiv.apply_symm_apply]

theorem semiConj_apply (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (g : V ≃ₗ[K] V) (v : V) :
    semiConj hF g v = F (g (F.symm v)) :=
  rfl

@[expose] def semiConjHom (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) :
    (V ≃ₗ[K] V) →* (V ≃ₗ[K] V) where
  toFun := semiConj hF
  map_one' := LinearEquiv.ext fun v => by
    rw [semiConj_apply]
    exact F.apply_symm_apply v
  map_mul' g h := LinearEquiv.ext fun v => by
    simp only [LinearEquiv.mul_apply, semiConj_apply, AddEquiv.symm_apply_apply]

theorem semiConjHom_apply (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (g : V ≃ₗ[K] V) :
    semiConjHom hF g = semiConj hF g :=
  rfl

variable {Q : QuadraticForm K V}

theorem semiConj_mem_orthogonalGroup (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) {μ : K}
    (hQ : ∀ v, Q (F v) = μ * σ (Q v)) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    semiConj hF g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [semiConj_apply, hQ, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg, ← hQ,
    AddEquiv.apply_symm_apply]

theorem semiConj_mem_orthDerived (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) {μ : K}
    (hQ : ∀ v, Q (F v) = μ * σ (Q v)) {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q) :
    semiConj hF g ∈ orthDerived Q := by
  have hO : (TauCeti.QuadraticMap.orthogonalGroup Q).map (semiConjHom hF) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨h, hh, rfl⟩
    exact semiConj_mem_orthogonalGroup hF hQ hh
  have hg' : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := hg
  have h := Subgroup.mem_map_of_mem (semiConjHom hF) hg'
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono hO hO h

end SemiConj

theorem eq_one_of_mem_scalars_of_mem_orthDerived {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hodd : Odd (Module.finrank K V)) {v₀ : V} (hv₀ : Q v₀ ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ orthDerived Q) (hs : g ∈ scalars K V) : g = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hs
  have hO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hc2 : c ^ 2 = 1 := by
    have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hO hg) v₀
    rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h
    have h' : (c ^ 2 - 1) * Q v₀ = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hv₀)
  have hdet : LinearEquiv.det g = 1 := by
    have hle : orthDerived Q ≤ commutator (V ≃ₗ[K] V) := Subgroup.commutator_mono le_top le_top
    exact MonoidHom.mem_ker.mp
      ((hle.trans (Abelianization.commutator_subset_ker LinearEquiv.det)) hg)
  have hlin : (g : V →ₗ[K] V) = c • LinearMap.id := LinearMap.ext fun v => by
    rw [LinearEquiv.coe_coe, hc]
    rfl
  have hcd : c ^ Module.finrank K V = 1 := by
    have h := congrArg Units.val hdet
    rw [LinearEquiv.coe_det, hlin, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Units.val_one] at h
    exact h
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at hcd
  exact LinearEquiv.ext fun v => by
    rw [hc, hcd, one_smul]
    rfl

section Induced

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem commute_of_inducedBySemilinear
    (htriv : ∀ h : V ≃ₗ[K] V, h ∈ orthDerived Q → h ∈ scalars K V → h = 1)
    {σ : K ≃+* K} {F : V ≃+ V} (hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v) {μ : K}
    (hQ : ∀ v, Q (F v) = μ * σ (Q v)) {α : MulAut (ProjOrthDerived Q)}
    (hind : ∀ g g' : orthDerived Q,
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
        α (QuotientGroup.mk g) = QuotientGroup.mk g')
    {g : orthDerived Q} (hfix : α (QuotientGroup.mk g) = QuotientGroup.mk g) (v : V) :
    F ((g : V ≃ₗ[K] V) v) = (g : V ≃ₗ[K] V) (F v) := by
  obtain ⟨g', hg'⟩ : ∃ g' : orthDerived Q, (g' : V ≃ₗ[K] V) = semiConj hF g :=
    ⟨⟨_, semiConj_mem_orthDerived hF hQ g.2⟩, rfl⟩
  have h1 := hind g g' fun w => by rw [hg', semiConj_apply]
  rw [hfix, QuotientGroup.eq] at h1
  have h2 := htriv _ (g⁻¹ * g').2 (Subgroup.mem_subgroupOf.mp h1)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_one, hg'] at h2
  have h4 := (LinearEquiv.congr_fun h2 (F v)).symm
  rwa [semiConj_apply, AddEquiv.symm_apply_apply] at h4

theorem eq_conj_of_inducedBySemilinear {F : V ≃+ V} {α : MulAut (ProjOrthDerived Q)}
    (hind : ∀ g g' : orthDerived Q,
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
        α (QuotientGroup.mk g) = QuotientGroup.mk g')
    (T : orthDerived Q) {c : K} (hc : c ≠ 0) (hFT : ∀ v, F v = c • (T : V ≃ₗ[K] V) v) :
    α = MulAut.conj (QuotientGroup.mk T) := by
  have hsymm : ∀ v, F.symm v = c⁻¹ • (T : V ≃ₗ[K] V).symm v := by
    intro v
    apply F.injective
    rw [AddEquiv.apply_symm_apply, hFT, map_smul, LinearEquiv.apply_symm_apply, smul_smul,
      mul_inv_cancel₀ hc, one_smul]
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [hind g (T * g * T⁻¹) fun v => ?_, MulAut.conj_apply, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hsymm, map_smul, hFT, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rfl

end Induced

end CFSG.ComponentClassification.HarrisLit.T1
