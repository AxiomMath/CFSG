module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCSpLin
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCSp
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddSymplectic

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare QuaternionMatrices
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher OddSymplectic
open CFSG.ComponentClassification CatalogueBSymplecticB CatalogueBAlternatingIsometry
  CatalogueBSymplecticRepresentation CatalogueBLinearTwoDescent CatalogueBOrthogonalDescent
open SymplecticHigher FixedFourGroup

theorem spWit_scalar_square {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ} (hr : 3 ≤ r)
    (hdim : finrank K V = 2 * r) {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V}
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd0 : d ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) :
    SpWit B A := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK' : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hε, hsqcase, hnscase⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hK
    n.pos hK' (by omega : 1 ≤ r) hdim hB hBnd hAns hd0 hAA hAμ
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    obtain ⟨hP, hM, h1, h2'⟩ := hsqcase l hl
    rcases hε with hε | hε
    · obtain ⟨-, hAp, -, hNp, -, e, he⟩ := h1 hε
      exact spWit_split hK hP hM hAp hNp e he
    · obtain ⟨-, -, hrp, -, -, -, e, he, -⟩ := h2' hε
      exact spWit_paired hK hr hrp e he
  · push Not at hsq
    obtain ⟨-, -, hcardE, hrankE, bar, -, hbar, -, hc1, hc2⟩ := hnscase hsq
    rcases hε with hε | hε
    · obtain ⟨BE, -, hBEa, hBEn, -, hiff⟩ := hc1 hε
      exact spWit_field_alt hK hAA hsq BE hBEa hBEn hiff
    · obtain ⟨hf, -, hsymm, hsep, hiff⟩ := hc2 hε
      exact spWit_field_herm hAA hsq hK hℓ n.pos hK' hcardE (by rw [hrankE]; exact hr) bar
        hbar hf hsymm hsep hiff

section Cases

variable {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {V : Type} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
  (hnd : B.Nondegenerate)
include hK hB hnd

theorem exists_odd_linear {r : ℕ} (hr : 3 ≤ r) (hdim : finrank K V = 2 * r) (A : V ≃ₗ[K] V)
    (hAns : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) (d : Kˣ)
    (hsq : ∀ x, A (A x) = (d : K) • x) (μ : Kˣ) (hsim : ∀ x y, B (A x) (A y) = (μ : K) * B x y) :
    ∃ T : Set (projectiveSymplectic B),
      (∀ t ∈ T, projectiveConjugation B A μ hsim t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := by
  set A' := (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm A with hA'
  obtain ⟨T, hT, hTo, hT2⟩ := exists_odd_of_spWit (spWit_scalar_square hK hr hdim hB hnd
    (A := A') (fun c h => hAns c h) d.ne_zero (LinearMap.ext fun v => hsq v) (μ := (μ : K))
    fun v w => hsim v w)
  refine ⟨(symplecticProjEquiv B).toMonoidHom '' T, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg, rfl⟩ := hT hw
      change projectiveConjugation B A μ hsim (symplecticProjEquiv B (symplecticProj B g)) =
        symplecticProjEquiv B (symplecticProj B g)
      rw [symplecticProjEquiv_proj, projectiveConjugation_mk]
      refine congrArg _ (Subtype.ext ?_)
      have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hg)
      have h2 : (sesqIsometryEquiv B g).val * A = A * (sesqIsometryEquiv B g).val :=
        LinearEquiv.ext fun v => congrArg (fun u : LinearMap.GeneralLinearGroup K V =>
          (u : Module.End K V) v) hcomm
      rw [similitudeConjugation_val, mul_inv_eq_iff_eq_mul, h2]
    · change Odd (orderOf (symplecticProjEquiv B w))
      rw [MulEquiv.orderOf_eq]
      exact hTo w hw
  · rw [← MonoidHom.map_closure, Subgroup.card_map_of_injective
      (f := (symplecticProjEquiv B).toMonoidHom) (symplecticProjEquiv B).injective]
    exact hT2

theorem exists_odd_semilinear (hdim : 0 < finrank K V) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1)
    (hσ : σ ≠ 1) (τ₀ : V ≃+ V) (μ l : Kˣ) (hsemi : ∀ a x, τ₀ (a • x) = σ a • τ₀ x)
    (hform : ∀ x y, B (τ₀ x) (τ₀ y) = (μ : K) * σ (B x y))
    (hsquare : ∀ x, τ₀ (τ₀ x) = (l : K) • x) :
    ∃ T : Set (projectiveSymplectic B),
      (∀ t ∈ T, projectiveSemilinearConjugation B σ τ₀ μ hsemi hform t = t ∧
        Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
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
  obtain ⟨ψk, hψk, -, hψks⟩ := exists_sl2_sp _ hB0a hB0n
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
  have hfix : ∀ z, projectiveSemilinearConjugation B σ τ₀ μ hsemi hform
      (QuotientGroup.mk' (scalarSigns B) (ψ z)) = QuotientGroup.mk' (scalarSigns B) (ψ z) :=
    fun z => by
      rw [projectiveSemilinearConjugation_mk]
      have hz : (e.symm z).val ∈
          FixedCommutingProduct.fixedSubgroup (semilinearConjugation B σ τ₀ μ hsemi hform) := by
        rw [fixed_semilinearConjugation_eq B σ τ₀ μ hsemi hform]
        exact (e.symm z).prop
      exact congrArg _ hz
  let φ0 := (sesqIsometryEquiv _).toMonoidHom.comp (ψk.codRestrict _ hψk)
  let θ := (QuotientGroup.mk' (scalarSigns B)).comp (ψ.comp φ0)
  have hns : φ0 (slQuatI _) ∉ scalarSigns _ :=
    not_mem_scalarSigns _
      (by
        by_contra h
        push Not at h
        exact hψks 1 (LinearMap.ext fun w => by
          rw [LinearMap.smul_apply, one_smul, Module.End.one_apply]
          exact h w))
      (by
        by_contra h
        push Not at h
        exact hψks (-1) (LinearMap.ext fun w => by
          rw [LinearMap.smul_apply, neg_one_smul, Module.End.one_apply]
          exact h w))
  have hθx : θ (slQuatI _) ≠ 1 := fun h =>
    map_not_mem_scalarSigns _ ψ hψinj hψn hns ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨hS, hSo⟩ := elementary_closure_odd h2k 2
  obtain ⟨hTo, hT2⟩ := odd_closure_image θ hS hSo slQuatI_pow_four hθx
  refine ⟨θ '' LinearGroups.elementarySet 2 _, fun t ht => ⟨?_, hTo t ht⟩, hT2⟩
  obtain ⟨s, -, rfl⟩ := ht
  exact hfix (φ0 s)

end Cases

theorem exists_fixed_odd_statedSp {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) {r : ℕ}
    (hr : 3 ≤ r) (α : MulAut (StatedProj (StatedSp r K)))
    (hα : α ^ 2 = 1) (h1 : α ≠ 1) :
    ∃ T : Set (StatedProj (StatedSp r K)), (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  have hr1 : 1 ≤ r := by omega
  have hdim : finrank K (Fin r ⊕ Fin r → K) = 2 * r := SymplecticFlag.finrank_standard
  have : Nontrivial (Fin r ⊕ Fin r → K) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hpull : ∀ β : MulAut (projectiveSymplectic (pairedSympForm K r)),
      (∀ x, projectiveStatedEquiv hr1 (α x) = β (projectiveStatedEquiv hr1 x)) →
      (∃ T : Set (projectiveSymplectic (pairedSympForm K r)),
        (∀ t ∈ T, β t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T)) →
      ∃ T : Set (StatedProj (StatedSp r K)), (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧
        2 ∣ Nat.card (closure T) := fun β hβ ⟨T, hT, h2⟩ => by
    have hcongr : MulAut.congr (projectiveStatedEquiv hr1) α = β := MulEquiv.ext fun y => by
      rw [congr_apply_eq, hβ, MulEquiv.apply_symm_apply]
    exact CatLeafProof.Q81P2.exists_odd_congr (projectiveStatedEquiv hr1) α
      (by rw [hcongr]; exact hT) h2
  obtain ⟨A, σ, hα', hσ2, ⟨d, hd⟩, hlin, -⟩ :=
    (odd_symplectic_automorphism_semilinear_representation hK (by omega)).2.2 α
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
    exact exists_odd_linear hK _ SymplecticFlag.pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate hr hdim _
      (matrixLinIso_ne_smul_one _ (hlin rfl)) d (semilinearCoordMap_sq _ 1 hσ2 d hd) μ
      (matrix_similitude _ μ hμ)
  · refine hpull (projectiveSemilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) K) σ) μ
      (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ)) (fun x => by
        rw [hα']
        exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x) ?_
    exact exists_odd_semilinear hK _ SymplecticFlag.pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate (by rw [hdim]; omega) σ hσ2 hσ _ μ d
      (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ)
      (semilinearCoordMap_sq _ σ hσ2 d hd)

theorem oddSpHigherRow : OddSpHigherRow := by
  intro Y _ _ hY _ _ a ha hP
  obtain ⟨n, p, f, hn, hp2, ⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hY
  have : CharP K p := GSThmB.Cent516.charP_of_card hp hK
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : Finite (StatedProj (StatedSp n K)) := Finite.of_equiv _ e.toEquiv
  have hα2 : MulAut.congr e a ^ 2 = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hα1 : MulAut.congr e a ≠ 1 := fun h => by
    have h1 : a = 1 := (MulAut.congr e).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at ha
    exact absurd ha (by decide)
  exact (not_isPGroup_of_fixed_odd (exists_fixed_odd_statedSp hchar hn _ hα2 hα1)
    (L33.isPGroup_fixedPoints_congr e a hP)).elim

end CFSG.ComponentClassification.HarrisLit.L33.OC
