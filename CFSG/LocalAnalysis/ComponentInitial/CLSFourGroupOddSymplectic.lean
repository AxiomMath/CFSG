module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OddSymplectic

open Module CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification CatalogueBSymplecticB CatalogueBAlternatingIsometry
  CatalogueBSymplecticRepresentation CatalogueBLinearTwoDescent CatalogueBOrthogonalDescent
open SymplecticHigher CLSFourGroupScalarSquare FixedFourGroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Bridge

variable {F : Type} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
  (B : LinearMap.BilinForm F W)

theorem map_sesqUnitaryGroup :
    (sesqUnitaryGroup B).map (LinearMap.GeneralLinearGroup.generalLinearEquiv F W).toMonoidHom =
      isometryGroup B := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_isometryGroup_iff]
  exact Iff.rfl

@[expose] def sesqIsometryEquiv : sesqUnitaryGroup B ≃* isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F W).subgroupMap (sesqUnitaryGroup B)).trans
    (MulEquiv.subgroupCongr (map_sesqUnitaryGroup B))

theorem sesqIsometryEquiv_apply (g : sesqUnitaryGroup B) (w : W) :
    (sesqIsometryEquiv B g).val w =
      ((g : LinearMap.GeneralLinearGroup F W) : Module.End F W) w :=
  rfl

theorem sesqIsometryEquiv_neg_one :
    sesqIsometryEquiv B ⟨-1, neg_one_mem_sesqUnitaryGroup B⟩ = negIsometry B :=
  Subtype.ext (LinearEquiv.ext fun w => by
    rw [sesqIsometryEquiv_apply, negIsometry_apply]
    simp)

theorem map_symplecticSignScalars :
    (symplecticSignScalars B).map (sesqIsometryEquiv B).toMonoidHom = scalarSigns B := by
  ext h
  rw [Subgroup.mem_map_equiv, mem_symplecticSignScalars, mem_scalarSigns_iff]
  constructor
  · rintro (h1 | h1)
    · left
      rw [← (sesqIsometryEquiv B).apply_symm_apply h,
        show (sesqIsometryEquiv B).symm h = 1 from Subtype.ext h1, map_one]
    · right
      rw [← (sesqIsometryEquiv B).apply_symm_apply h,
        show (sesqIsometryEquiv B).symm h = ⟨-1, neg_one_mem_sesqUnitaryGroup B⟩ from
          Subtype.ext h1, sesqIsometryEquiv_neg_one]
  · rintro (rfl | rfl)
    · left
      rw [map_one]
      rfl
    · right
      rw [← sesqIsometryEquiv_neg_one, MulEquiv.symm_apply_apply]

@[expose] def symplecticProjEquiv : SymplecticProj B ≃* projectiveSymplectic B :=
  QuotientGroup.congr (symplecticSignScalars B) (scalarSigns B) (sesqIsometryEquiv B)
    (map_symplecticSignScalars B)

theorem symplecticProjEquiv_proj (g : sesqUnitaryGroup B) :
    symplecticProjEquiv B (symplecticProj B g) =
      QuotientGroup.mk' (scalarSigns B) (sesqIsometryEquiv B g) :=
  QuotientGroup.congr_mk' _ _ _ _ g

end Bridge

section Quaternion

variable {F : Type} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
  (B : LinearMap.BilinForm F W)

theorem exists_four_of_quat {x y : isometryGroup B} (hxx : x * x = negIsometry B)
    (hyy : y * y = negIsometry B) (hxy : x * y = negIsometry B * (y * x))
    (hx : x ∉ scalarSigns B) (hy : y ∉ scalarSigns B) (hxy' : x * y ∉ scalarSigns B)
    {H : Subgroup (projectiveSymplectic B)} (hxH : QuotientGroup.mk' (scalarSigns B) x ∈ H)
    (hyH : QuotientGroup.mk' (scalarSigns B) y ∈ H) :
    ∃ V : Subgroup (projectiveSymplectic B), V ≤ H ∧ CFSG.IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  have hπ : ∀ g, QuotientGroup.mk' (scalarSigns B) g = 1 ↔ g ∈ scalarSigns B :=
    fun g => QuotientGroup.eq_one_iff g
  have hn : QuotientGroup.mk' (scalarSigns B) (negIsometry B) = 1 :=
    (hπ _).2 ((mem_scalarSigns_iff B _).2 (Or.inr rfl))
  have hpx : QuotientGroup.mk' (scalarSigns B) x * QuotientGroup.mk' (scalarSigns B) x = 1 := by
    rw [← map_mul, hxx, hn]
  have hpy : QuotientGroup.mk' (scalarSigns B) y * QuotientGroup.mk' (scalarSigns B) y = 1 := by
    rw [← map_mul, hyy, hn]
  have hpxy : QuotientGroup.mk' (scalarSigns B) x * QuotientGroup.mk' (scalarSigns B) y =
      QuotientGroup.mk' (scalarSigns B) y * QuotientGroup.mk' (scalarSigns B) x := by
    rw [← map_mul, hxy, map_mul, hn, one_mul, map_mul]
  have hpne : QuotientGroup.mk' (scalarSigns B) x ≠ QuotientGroup.mk' (scalarSigns B) y :=
    fun h => hxy' ((hπ _).1 (by rw [map_mul, ← h, hpx]))
  obtain ⟨V, -, hVle, hV, hVc⟩ := FourGroup.exists_kleinFour hpx hpy hpxy
    (fun h => hx ((hπ x).1 h)) (fun h => hy ((hπ y).1 h)) hpne
  exact ⟨V, hVle H hxH hyH, hV, hVc⟩

theorem not_mem_scalarSigns {x : isometryGroup B} (h1 : ∃ w, x.val w ≠ w)
    (h2 : ∃ w, x.val w ≠ -w) : x ∉ scalarSigns B := fun h => by
  rcases (mem_scalarSigns_iff B x).1 h with h | h
  · obtain ⟨w, hw⟩ := h1
    exact hw (by rw [h]; rfl)
  · obtain ⟨w, hw⟩ := h2
    exact hw (by rw [h, negIsometry_apply])

theorem exists_quat_isometry [Finite F] (hF : ringChar F ≠ 2) [FiniteDimensional F W]
    [Nontrivial W] (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ x y : isometryGroup B, x * x = negIsometry B ∧ y * y = negIsometry B ∧
      x * y = negIsometry B * (y * x) ∧ x ∉ scalarSigns B ∧ y ∉ scalarSigns B ∧
      x * y ∉ scalarSigns B := by
  obtain ⟨i, j, hi, hj, hii, hjj, hij, hin, hjn, hijn⟩ := exists_quat_sp hF B hB hnd
  have hns : ∀ g : sesqUnitaryGroup B,
      (∀ a : F, ((g : LinearMap.GeneralLinearGroup F W) : Module.End F W) ≠ a • 1) →
        sesqIsometryEquiv B g ∉ scalarSigns B := fun g hg =>
    not_mem_scalarSigns B
      (by
        by_contra h
        push Not at h
        exact hg 1 (LinearMap.ext fun w => by
          rw [← sesqIsometryEquiv_apply, h w, one_smul]
          rfl))
      (by
        by_contra h
        push Not at h
        exact hg (-1) (LinearMap.ext fun w => by
          rw [← sesqIsometryEquiv_apply, h w, neg_one_smul]
          rfl))
  have hneg := sesqIsometryEquiv_neg_one B
  refine ⟨sesqIsometryEquiv B ⟨i, hi⟩, sesqIsometryEquiv B ⟨j, hj⟩, ?_, ?_, ?_, hns _ hin,
    hns _ hjn, ?_⟩
  · rw [← map_mul, ← hneg]
    exact congrArg _ (Subtype.ext hii)
  · rw [← map_mul, ← hneg]
    exact congrArg _ (Subtype.ext hjj)
  · rw [← map_mul, ← map_mul, ← hneg, ← map_mul]
    refine congrArg _ (Subtype.ext ?_)
    change i * j = -1 * (j * i)
    rw [hij, neg_one_mul]
  · rw [← map_mul]
    exact hns ⟨i * j, mul_mem hi hj⟩ hijn

theorem map_not_mem_scalarSigns {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {B' : LinearMap.BilinForm K V} (ψ : isometryGroup B →* isometryGroup B')
    (hψ : Function.Injective ψ) (hn : ψ (negIsometry B) = negIsometry B') {x : isometryGroup B}
    (hx : x ∉ scalarSigns B) : ψ x ∉ scalarSigns B' := fun h => by
  rcases (mem_scalarSigns_iff B' _).1 h with h | h
  · exact hx ((mem_scalarSigns_iff B x).2 (Or.inl (hψ (by rw [h, map_one]))))
  · exact hx ((mem_scalarSigns_iff B x).2 (Or.inr (hψ (by rw [h, hn]))))

end Quaternion

section Cases

variable {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {V : Type*} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
  (hnd : B.Nondegenerate)
include hK hB hnd

theorem exists_four_linear {r : ℕ} (hr : 2 ≤ r) (hdim : finrank K V = 2 * r) (A : V ≃ₗ[K] V)
    (hAns : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) (d : Kˣ)
    (hsq : ∀ x, A (A x) = (d : K) • x) (μ : Kˣ) (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) :
    ∃ V' : Subgroup (projectiveSymplectic B),
      V' ≤ fixedSubgroup (projectiveConjugation B A μ hsim) ∧ CFSG.IsElementaryAbelian 2 V' ∧
        Nat.card V' = 4 := by
  set A' := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm A with hA'
  obtain ⟨W, hW, hWab, hWc⟩ := odd_symplectic_scalar_square_centralizer_projective_four_group hK
    hr hdim hB hnd (A := A') (fun c h => hAns c h) d.ne_zero
    (LinearMap.ext fun v => hsq v) (μ := (μ : K)) (fun v w => hsim v w)
  refine ⟨W.map (symplecticProjEquiv B).toMonoidHom, ?_, hWab.map _, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hW hw
    change projectiveConjugation B A μ hsim (symplecticProjEquiv B (symplecticProj B g)) =
      symplecticProjEquiv B (symplecticProj B g)
    rw [symplecticProjEquiv_proj, projectiveConjugation_mk]
    refine congrArg _ (Subtype.ext ?_)
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hg)
    have h2 : (sesqIsometryEquiv B g).val * A = A * (sesqIsometryEquiv B g).val :=
      LinearEquiv.ext fun v => congrArg (fun u : LinearMap.GeneralLinearGroup K V =>
        (u : Module.End K V) v) hcomm
    rw [similitudeConjugation_val, mul_inv_eq_iff_eq_mul, h2]
  · rw [Subgroup.card_map_of_injective (f := (symplecticProjEquiv B).toMonoidHom)
      (symplecticProjEquiv B).injective]
    exact hWc

theorem exists_four_semilinear (hdim : 0 < finrank K V) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1)
    (hσ : σ ≠ 1) (τ₀ : V ≃+ V) (μ l : Kˣ) (hsemi : ∀ a x, τ₀ (a • x) = σ a • τ₀ x)
    (hform : ∀ x y, B (τ₀ x) (τ₀ y) = (μ : K) * σ (B x y))
    (hsquare : ∀ x, τ₀ (τ₀ x) = (l : K) • x) :
    ∃ V' : Subgroup (projectiveSymplectic B),
      V' ≤ fixedSubgroup (projectiveSemilinearConjugation B σ τ₀ μ hsemi hform) ∧
        CFSG.IsElementaryAbelian 2 V' ∧ Nat.card V' = 4 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2 hσ
    h2 hdim B hB hnd τ₀ μ l hsemi hform hsquare
  obtain ⟨-, -, -, -, hfin, hrank, -, hB0a, hB0n, j, e, hj, -, -, -, he, -⟩ := hall b c hb hc
  have h2k : ringChar (fixedSubfield K σ) ≠ 2 := fun h => by
    have hc2 := ringChar.Nat.cast_ringChar (R := fixedSubfield K σ)
    rw [h] at hc2
    apply h2
    have h3 := map_natCast (fixedSubfield K σ).subtype 2
    rw [hc2, map_zero] at h3
    exact_mod_cast h3.symm
  have : Nontrivial (originalFixedSubspace σ τ₀ b hsemi) :=
    Module.nontrivial_of_finrank_pos (R := fixedSubfield K σ) (by rw [hrank]; exact hdim)
  obtain ⟨x, y, hxx, hyy, hxy, hx, hy, hxy'⟩ := exists_quat_isometry _ h2k hB0a hB0n
  have hext : ∀ {f g : V ≃ₗ[K] V},
      (∀ w : originalFixedSubspace σ τ₀ b hsemi, f w = g w) → f = g := fun {f g} h => by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨t, rfl⟩ := j.surjective v
    induction t using TensorProduct.inductionOn with
    | tmul a w => rw [hj, map_smul, map_smul, h]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  let ψ := (semilinearSymplecticCentralizer B τ₀).subtype.comp e.symm.toMonoidHom
  have hψinj : Function.Injective ψ :=
    (Subgroup.subtype_injective _).comp e.symm.injective
  have hψn : ψ (negIsometry _) = negIsometry B := Subtype.ext (hext fun w => by
    have hw := he (negIsometry _) 1 w
    rw [one_smul, one_smul] at hw
    change (e.symm (negIsometry _)).val.val (w : V) = -(w : V)
    rw [hw, negIsometry_apply, Submodule.coe_neg])
  have hfix : ∀ z, QuotientGroup.mk' (scalarSigns B) (ψ z) ∈
      fixedSubgroup (projectiveSemilinearConjugation B σ τ₀ μ hsemi hform) := fun z => by
    change projectiveSemilinearConjugation B σ τ₀ μ hsemi hform
      (QuotientGroup.mk' (scalarSigns B) (ψ z)) = QuotientGroup.mk' (scalarSigns B) (ψ z)
    rw [projectiveSemilinearConjugation_mk]
    have hz : (e.symm z).val ∈
        fixedSubgroup (semilinearConjugation B σ τ₀ μ hsemi hform) := by
      rw [fixed_semilinearConjugation_eq B σ τ₀ μ hsemi hform]
      exact (e.symm z).prop
    exact congrArg _ hz
  refine exists_four_of_quat B (x := ψ x) (y := ψ y) ?_ ?_ ?_
    (map_not_mem_scalarSigns _ ψ hψinj hψn hx) (map_not_mem_scalarSigns _ ψ hψinj hψn hy) ?_
    (hfix x) (hfix y)
  · rw [← map_mul, hxx, hψn]
  · rw [← map_mul, hyy, hψn]
  · rw [← map_mul, hxy, map_mul, hψn, map_mul]
  · rw [← map_mul]
    exact map_not_mem_scalarSigns _ ψ hψinj hψn hxy'

end Cases

theorem exists_fixed_four_group_statedSp {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) {r : ℕ} (hr : 2 ≤ r) (α : MulAut (StatedProj (StatedSp r K)))
    (hα : α ^ 2 = 1) :
    ∃ V : Subgroup (StatedProj (StatedSp r K)), V ≤ fixedSubgroup α ∧
      CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  have hr1 : 1 ≤ r := by omega
  have hdim : finrank K (Fin r ⊕ Fin r → K) = 2 * r := SymplecticFlag.finrank_standard
  have : Nontrivial (Fin r ⊕ Fin r → K) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hpull : ∀ β : MulAut (projectiveSymplectic (pairedSympForm K r)),
      (∀ x, projectiveStatedEquiv hr1 (α x) = β (projectiveStatedEquiv hr1 x)) →
      (∃ V' : Subgroup (projectiveSymplectic (pairedSympForm K r)), V' ≤ fixedSubgroup β ∧
        CFSG.IsElementaryAbelian 2 V' ∧ Nat.card V' = 4) →
      ∃ V : Subgroup (StatedProj (StatedSp r K)), V ≤ fixedSubgroup α ∧
        CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := fun β hβ ⟨V', hV', hab, hc⟩ => by
    have hcongr : MulAut.congr (projectiveStatedEquiv hr1) α = β := MulEquiv.ext fun y => by
      rw [congr_apply_eq, hβ, MulEquiv.apply_symm_apply]
    exact exists_four_group_le_fixedSubgroup_of_congr _ α (hcongr ▸ hV') hab hc
  by_cases h1 : α = 1
  · subst h1
    refine hpull 1 (fun x => rfl) ?_
    obtain ⟨x, y, hxx, hyy, hxy, hx, hy, hxy'⟩ := exists_quat_isometry (pairedSympForm K r) hK
      SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    obtain ⟨V', -, hab, hc⟩ := exists_four_of_quat _ hxx hyy hxy hx hy hxy' (H := ⊤) trivial
      trivial
    exact ⟨V', fun v _ => rfl, hab, hc⟩
  · obtain ⟨A, σ, hα', hσ2, ⟨d, hd⟩, hlin, -⟩ :=
      (odd_symplectic_automorphism_semilinear_representation hK hr).2.2 α
        (by rw [← sq]; exact hα) h1
    set μ := multiplierUnit A
    have hμ := multiplierUnit_spec A
    by_cases hσ : σ = 1
    · subst hσ
      refine hpull (projectiveConjugation (pairedSympForm K r)
        (matrixLinIso (A : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) K)) μ
        (matrix_similitude _ μ hμ)) (fun x => by
          rw [hα', map_one, mul_one]
          exact projectiveStatedEquiv_conjAut hr1 A μ hμ x) ?_
      exact exists_four_linear hK _ SymplecticFlag.pairedSympForm_isAlt
        SymplecticFlag.pairedSympForm_nondegenerate hr hdim _
        (matrixLinIso_ne_smul_one _ (hlin rfl)) d (semilinearCoordMap_sq _ 1 hσ2 d hd) μ
        (matrix_similitude _ μ hμ)
    · refine hpull (projectiveSemilinearConjugation (pairedSympForm K r) σ
        (semilinearCoordMap (A : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) K) σ) μ
        (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ)) (fun x => by
          rw [hα']
          exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x) ?_
      exact exists_four_semilinear hK _ SymplecticFlag.pairedSympForm_isAlt
        SymplecticFlag.pairedSympForm_nondegenerate (by rw [hdim]; omega) σ hσ2 hσ _ μ d
        (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ)
        (semilinearCoordMap_sq _ σ hσ2 d hd)

theorem odd_symplectic_all_involution_fixed_four_group (L : Type) [Group L] {p f r : ℕ}
    (hp : p ≠ 2) (hL : StatedClassicalModel L .PSp r p f) (α : MulAut L) (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨⟨hprime, hf, hr, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have : CharP K p := finite_field_prime_power_characteristic hprime hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp
  obtain ⟨V, hV, hVab, hVc⟩ := exists_fixed_four_group_statedSp hchar hr (MulAut.congr e α)
    (by rw [← map_pow, hα, map_one])
  exact exists_four_group_le_fixedSubgroup_of_congr e α hV hVab hVc

end CFSG.LocalAnalysis.ComponentInitial.OddSymplectic
