module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFour
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUMat

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.GSThmB.Catalog7L4EU
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar)
open CFSG.LinearGroups Matrix

section Orth

variable {k : Type} [Field k] [Finite k] {W : Type} [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]

theorem exists_other_factor (Q : QuadraticForm k W) (hQ : Q.polarBilin.Nondegenerate)
    (hodd : Odd (Nat.card k)) (hdim : finrank k W = 4)
    (hsplit : ∃ S : Submodule k W, finrank k S = 2 ∧ ∀ x ∈ S, Q x = 0) (h5 : 5 ≤ Nat.card k)
    {Y : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hY : CFSG.IsComponent Y) :
    ∃ (R₂ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
      (t₂ s₂ : TauCeti.QuadraticMap.orthogonalGroup Q), ⁅R₂, R₂⁆ = R₂ ∧
      (∀ x ∈ Y, ∀ y ∈ R₂, x * y = y * x) ∧ t₂ ∈ R₂ ∧ (∀ v, t₂.val (t₂.val v) = -v) ∧
      t₂ * s₂ ≠ s₂ * t₂ := by
  classical
  obtain ⟨-, -, -, hsplitm, -, -, -⟩ :=
    orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
      (Or.inl ⟨hodd, Or.inr (Or.inl hdim)⟩)
  obtain ⟨ψ₀, eD, -, heD, hsup, hq₁, hq₂, hn₁, hn₂, hcomm⟩ :=
    hsplitm hdim hsplit (by omega) (by omega)
  have hact : ∀ z v, (eD.symm (specialRho z)).val v =
      ψ₀.symm (z.1.val * ψ₀ v * (z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) k).val) := by
    intro z v
    apply ψ₀.injective
    rw [LinearEquiv.apply_symm_apply, ← specialRho_apply z (ψ₀ v)]
    have h1 := heD (eD.symm (specialRho z)) (ψ₀ v)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨J, hJJ, hJs⟩ := OddClassSelector.exists_rotation k
  have hone : (1 : Matrix.SpecialLinearGroup (Fin 2) k).val = 1 := rfl
  obtain ⟨D, hD⟩ : ∃ D : Matrix.SpecialLinearGroup (Fin 2) k, D * J ≠ J * D := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
      (Subgroup.mem_center_iff.mpr hcon)
    apply hJs r
    rw [← hr, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rcases LocalAnalysis.ComponentInitial.eq_or_eq_of_isComponent_of_commutator_eq_sup hY hsup
    hq₁ hq₂ hn₁ hn₂ with h' | h'
  · refine ⟨_, eD.symm (specialRho (1, J⁻¹)), eD.symm (specialRho (1, D)),
      Subgroup.isPerfect_iff.mp hq₂.1, ?_, ⟨specialRho (1, J⁻¹), ⟨J⁻¹, rfl⟩, rfl⟩,
      fun v => ?_, fun he => ?_⟩
    · rw [h']
      exact hcomm
    · rw [hact, hact, LinearEquiv.apply_symm_apply]
      simp only [inv_inv, hone, Matrix.one_mul, Matrix.mul_assoc, hJJ, Matrix.mul_neg,
        Matrix.mul_one, map_neg, LinearEquiv.symm_apply_apply]
    · have he' : (specialRho.comp (MonoidHom.inr _ _)) (J⁻¹ * D) =
          (specialRho.comp (MonoidHom.inr _ _)) (D * J⁻¹) := by
        apply eD.symm.injective
        rw [map_mul, map_mul, map_mul, map_mul]
        exact he
      have he'' := specialRho_inr_injective k he'
      apply hD
      calc D * J = J * (J⁻¹ * D) * J := by group
        _ = J * D := by rw [he'']; group
  · refine ⟨_, eD.symm (specialRho (J, 1)), eD.symm (specialRho (D, 1)),
      Subgroup.isPerfect_iff.mp hq₁.1, ?_, ⟨specialRho (J, 1), ⟨J, rfl⟩, rfl⟩,
      fun v => ?_, fun he => ?_⟩
    · rw [h']
      exact fun x hx y hy => (hcomm y hy x hx).symm
    · rw [hact, hact, LinearEquiv.apply_symm_apply]
      simp only [inv_one, hone, Matrix.mul_one, ← Matrix.mul_assoc, hJJ, Matrix.neg_mul,
        Matrix.one_mul, map_neg, LinearEquiv.symm_apply_apply]
    · have he' : (specialRho.comp (MonoidHom.inl _ _)) (J * D) =
          (specialRho.comp (MonoidHom.inl _ _)) (D * J) := by
        apply eD.symm.injective
        rw [map_mul, map_mul, map_mul, map_mul]
        exact he
      exact hD (specialRho_inl_injective k he').symm

end Orth

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem anti_witness (hp : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1) {z : K}
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = z • 1)
    {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : CFSG.Assembly.IsComponentOf Y (fixedSubgroup (antiConjA h hAu)))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X) :
    (∃ (E' : Type) (_ : Field E') (_ : Finite E'), Nat.card E' = Nat.card h.fixedField ^ 2 ∧
        Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 E')) ∨
      ∃ (Y₂ : Subgroup (sesqUnitaryGroup (stdHermForm h 4)))
        (T : sesqUnitaryGroup (stdHermForm h 4)),
        ⁅Y₂, Y₂⁆ = Y₂ ∧ T ∈ Y₂ ∧ (∀ y ∈ Y, ∀ w ∈ Y₂, y * w = w * y) ∧
        unitaryOp T * unitaryOp T = -1 ∧ T ∉ sesqNormOneScalars h (stdHermForm h 4) := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite K := h.finite
  have : CharP K p := h.charP
  have hK : Nat.card h.fixedField = p ^ f := h.card_fixedField
  have hKodd : Odd (Nat.card h.fixedField) := by rw [hK]; exact hodd.pow
  have hτ₀ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hτ₀B := CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAA
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, det_zero, show (A : Matrix (Fin 4) (Fin 4) K).map h.bar =
      h.bar.mapMatrix (A : Matrix (Fin 4) (Fin 4) K) from rfl, ← RingHom.map_det] at h1
    have hA0 : (A : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero hA0 (fun h0 => hA0 ((map_eq_zero h.bar).1 h0)) h1
  have hμ : ∀ v, antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
      (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) v) = ((Units.mk0 z hz0 : Kˣ) : K) • v :=
    CatFactsL4U4.StabU.antiunitaryMap_sq h _ hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
    (stdHermForm_separatingLeft h 4) _ hτ₀ hτ₀B (Units.mk0 z hz0) hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) :=
    finite_conjFixed
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY := Subgroup.subgroupOfEquivOfLe hY.1
  have hσ₁k := OddClassSelector.ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp h1
  have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
  rcases hμ1 with hμ1 | hμ1
  swap
  ·
    exfalso
    obtain ⟨B', -, halt, hnd, -, Φ, -⟩ := hB2 hμ1
    exact OddClassSelector.sp_component_false h.prime hp h.one_le hK B' halt hnd
      (by rw [hfinW, Module.finrank_fin_fun]) ((fixedCommutingEquiv h _ hτ₀ hτ₀B).trans Φ) hY₁
      (σ.comp eY.toMonoidHom) hσ₁k hs
  obtain ⟨B', -, hsym, hnd, Φ, hΦ⟩ := hB1 hμ1
  have hQ' : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
    rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
    exact hnd
  have hdim : Module.finrank h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))) = 4 := by
    rw [hfinW, Module.finrank_fin_fun]
  obtain ⟨Φ', hΦ'⟩ : ∃ Φ' : fixedSubgroup (antiConjA h hAu) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B'),
      ∀ (g : fixedSubgroup (antiConjA h hAu))
        (w : conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))),
        (((Φ' g).val w : conjFixed h ((b : K) • antiunitaryMap h
          (A : Matrix (Fin 4) (Fin 4) K))) : Fin 4 → K) =
          unitaryOp (g : sesqUnitaryGroup (stdHermForm h 4)) (w : Fin 4 → K) :=
    ⟨(fixedCommutingEquiv h _ hτ₀ hτ₀B).trans
      (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2))),
      fun g w => hΦ (fixedCommutingEquiv h _ hτ₀ hτ₀B g) w⟩
  have hY' := isComponent_map_of_isComponent Φ' hY₁
  let eYY' : Y ≃* (Y.subgroupOf (fixedSubgroup (antiConjA h hAu))).map Φ'.toMonoidHom :=
    eY.symm.trans ((Y.subgroupOf _).equivMapOfInjective _ Φ'.injective)
  by_cases hsplit : ∃ S : Submodule h.fixedField
      (conjFixed h ((b : K) • antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))),
      Module.finrank h.fixedField S = 2 ∧
        ∀ x ∈ S, CatalogueBOrthogonalDescent.originalQuadratic B' x = 0
  swap
  · left
    obtain ⟨hquasi, E', _, _, hE', ⟨eC⟩⟩ :=
      commutator_equiv_psl_of_nonsplit _ hQ' hKodd hdim hsplit
    have hYeq := LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hY' hquasi
    have h3K : 3 ≤ Nat.card h.fixedField := by
      rw [hK]
      have h3p : 3 ≤ p := by have := h.prime.two_le; omega
      exact h3p.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
    have h3 : 3 < Nat.card E' := by rw [hE']; nlinarith
    exact ⟨E', inferInstance, inferInstance, hE', center_quotient_equiv_of_psl h3 σ hσs hσk
      ((eYY'.trans (MulEquiv.subgroupCongr hYeq)).trans eC)⟩
  right
  obtain ⟨hq5, -⟩ := component_equiv_sl_of_split _ hQ' hKodd hdim hsplit hY'
  obtain ⟨R₂, t₂, s₂, hR₂p, hcomm', ht₂R, ht₂t, hts⟩ :=
    exists_other_factor _ hQ' hKodd hdim hsplit hq5 hY'
  obtain ⟨ιF, hιFdef⟩ : ∃ ι : TauCeti.QuadraticMap.orthogonalGroup
      (CatalogueBOrthogonalDescent.originalQuadratic B') →* sesqUnitaryGroup (stdHermForm h 4),
      ι = (fixedSubgroup (antiConjA h hAu)).subtype.comp Φ'.symm.toMonoidHom := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m1 : sesqUnitaryGroup (stdHermForm h 4), unitaryOp m1 = -1 :=
    ⟨⟨-1, fun x y => by
      change (stdHermForm h 4) (-x) (-y) = (stdHermForm h 4) x y
      simp only [map_neg, LinearMap.neg_apply, neg_neg]⟩, rfl⟩
  have hm1F : m1 ∈ fixedSubgroup (antiConjA h hAu) := by
    refine (mem_fixed_unitaryConj h _ _ _ m1).mpr fun v => ?_
    rw [hm1]
    simp only [LinearMap.neg_apply, Module.End.one_apply, map_neg]
  have hT2 : ιF t₂ * ιF t₂ = m1 := by
    have h1 : t₂ * t₂ = Φ' ⟨m1, hm1F⟩ := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      apply Subtype.ext
      rw [hΦ', Subgroup.coe_mul, LinearEquiv.mul_apply, ht₂t, hm1]
      rfl
    rw [← map_mul, h1, hιFdef]
    simp
  refine ⟨R₂.map ιF, ιF t₂, ?_, ⟨t₂, ht₂R, rfl⟩, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hR₂p]
  · rintro y hy _ ⟨r, hr, rfl⟩
    have h1 := hcomm' (Φ' ⟨y, hY.1 hy⟩) ⟨⟨y, hY.1 hy⟩, mem_subgroupOf.mpr hy, rfl⟩ r hr
    have h2 := congrArg ιF h1
    simp only [hιFdef, map_mul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype] at h2 ⊢
    exact h2
  · change unitaryOp (ιF t₂ * ιF t₂) = -1
    rw [hT2]
    exact hm1
  ·
    intro hTZ
    apply hts
    have hinj : Function.Injective ιF := by
      rw [hιFdef]
      exact (Subgroup.subtype_injective _).comp Φ'.symm.injective
    apply hinj
    rw [map_mul, map_mul]
    exact mem_sesqNormOneScalars_commute hTZ (ιF s₂)

end CFSG.ComponentClassification.GSThmB.CF23I
