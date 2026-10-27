module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpCert
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpWitness
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSU
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.ComponentClassification.RestrictedStd
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_sq_add_sq (hodd : Odd (Nat.card K)) (c : K) : ∃ a b : K, a ^ 2 + b ^ 2 = c := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := K)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C c)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by decide) _)
    (by rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C]
    at hab
  exact ⟨a, b, by linear_combination hab⟩

theorem sp_half_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) {B : BilinForm K V} (hB : B.IsAlt) {M F : Submodule K V}
    (hdim : 6 ≤ finrank K M + finrank K F) (hMnd : (B.domRestrict₁₂ M M).Nondegenerate)
    (hFnd : (B.domRestrict₁₂ F F).Nondegenerate) {Y : Subgroup (isometryGroup B)}
    (hYF : ∀ y ∈ Y, ∀ f ∈ F, (y : V ≃ₗ[K] V) f = f)
    (ρ : Y →* isometryGroup (B.domRestrict₁₂ M M)) (hρi : Function.Injective ρ)
    (hρc : CFSG.IsComponent ρ.range)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσk : σ.ker ≤ center Y)
    (hs : SmallSource X)
    (hN : ∀ t s : isometryGroup B, t * t ∈ scalarSigns B → t ∉ scalarSigns B →
      (∀ y ∈ Y, y * t = t * y) → s * t = t * s → s ∈ normalizer (Y : Set (isometryGroup B))) :
    False := by
  classical
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ he hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
  have hMalt : (B.domRestrict₁₂ M M).IsAlt := fun x => hB x
  have hFalt : (B.domRestrict₁₂ F F).IsAlt := fun x => hB x
  by_cases h4 : 4 ≤ finrank K M
  · let eρ := MonoidHom.ofInjective hρi
    exact sp_component_false hℓ hℓ2 he hK (B.domRestrict₁₂ M M) hMalt hMnd h4 (MulEquiv.refl _)
      hρc (σ.comp eρ.symm.toMonoidHom)
      (ker_comp_le_center eρ.symm.toMonoidHom eρ.symm.injective σ hσk) hs
  · obtain ⟨k, hk⟩ := even_finrank (B.domRestrict₁₂ F F) hFalt hFnd
    have h1 := sp_eq_one_of_normalizer h2 hB hFnd (by omega) hYF hN
    have : Nontrivial ρ.range := CFSG.LocalCores.isQuasisimple_nontrivial hρc.1
    obtain ⟨⟨_, ⟨y, rfl⟩⟩, hy⟩ := exists_ne (1 : ρ.range)
    apply hy
    have hy1 : y = 1 := Subtype.ext (h1 y y.2)
    apply Subtype.ext
    change ρ y = 1
    rw [hy1, map_one]

theorem sp_linear_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) {r : ℕ} (hr : 3 ≤ r) (hdim : finrank K V = 2 * r)
    {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (T : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x, T (T x) = (d : K) • x)
    (hsim : ∀ x y, B (T x) (T y) = (μ : K) * B x y)
    (hnonscalar : ∀ c : K, T.toLinearMap ≠ c • (1 : Module.End K V))
    {Y : Subgroup (isometryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (symplecticOperatorCentralizer B T.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X)
    (hN : ∀ t s : isometryGroup B, t * t ∈ scalarSigns B → t ∉ scalarSigns B →
      (∀ y ∈ Y, y * t = t * y) → s * t = t * s → s ∈ normalizer (Y : Set (isometryGroup B))) :
    False := by
  classical
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ he hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  set Agl : LinearMap.GeneralLinearGroup K V := LinearMap.GeneralLinearGroup.ofLinearEquiv T
    with hAgl
  have hAA : (Agl : Module.End K V) * (Agl : Module.End K V) = (d : K) • 1 :=
    LinearMap.ext fun x => hsquare x
  obtain ⟨hε, hsplit, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2
    he hK (by omega) hdim hB hnd (A := Agl) hnonscalar (Units.ne_zero d) hAA hsim
  have hY' : CFSG.Assembly.IsComponentOf Y
      (symplecticOperatorCentralizer B (Agl : Module.End K V)) := hY
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY'.1).mp hY'
  let eY : Y.subgroupOf (symplecticOperatorCentralizer B (Agl : Module.End K V)) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hY'.1
  have hσ₁k := ker_comp_le_center eY.toMonoidHom eY.injective σ hσk
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hl
      exact Units.ne_zero d hl.symm
    obtain ⟨hP, hM, hpos, hneg⟩ := hsplit l hl
    have hc : IsCompl (eigenPlus l (Agl : Module.End K V))
        (eigenMinus l (Agl : Module.End K V)) :=
      isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 (by rw [hl]; exact hAA))
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    rcases hε with h1 | h1
    ·
      obtain ⟨-, -, -, hndP, hndM, e, he'⟩ := hpos h1
      let Φ := ((centralizerSimilitudeEquiv B Agl).trans e).trans
        (MulEquiv.prodCongr (sesqUnitaryIsometryEquiv _) (sesqUnitaryIsometryEquiv _))
      have hΦ1 : ∀ (g : symplecticOperatorCentralizer B (Agl : Module.End K V))
          (x : eigenPlus l (Agl : Module.End K V)),
          (((Φ g).1.val x : eigenPlus l (Agl : Module.End K V)) : V) =
            (g : isometryGroup B).val x := fun g x =>
        LinearMap.congr_fun (he' (centralizerSimilitudeEquiv B Agl g)).1 x
      have hΦ2 : ∀ (g : symplecticOperatorCentralizer B (Agl : Module.End K V))
          (x : eigenMinus l (Agl : Module.End K V)),
          (((Φ g).2.val x : eigenMinus l (Agl : Module.End K V)) : V) =
            (g : isometryGroup B).val x := fun g x =>
        LinearMap.congr_fun (he' (centralizerSimilitudeEquiv B Agl g)).2 x
      have hfix : ∀ (W : Submodule K V)
          (Ψ : symplecticOperatorCentralizer B (Agl : Module.End K V) →* isometryGroup
            (B.domRestrict₁₂ W W))
          (_ : ∀ g (x : W), (((Ψ g).val x : W) : V) = (g : isometryGroup B).val x)
          (_ : ∀ x ∈ Y.subgroupOf (symplecticOperatorCentralizer B (Agl : Module.End K V)),
            Ψ x = 1),
          ∀ y ∈ Y, ∀ f ∈ W, (y : V ≃ₗ[K] V) f = f := by
        intro W Ψ hΨ h1Ψ y hy f hf
        have h3 := hΨ (eY.symm ⟨y, hy⟩) ⟨f, hf⟩
        rw [h1Ψ _ (eY.symm ⟨y, hy⟩).2] at h3
        exact h3.symm
      rcases CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
          (isComponent_map_of_isComponent Φ hY₁) with h2' | h1'
      ·
        have h2'' : ∀ x ∈ Y.subgroupOf (symplecticOperatorCentralizer B (Agl : Module.End K V)),
            (Φ x).2 = 1 := fun x hx => h2' _ (mem_map_of_mem _ hx)
        obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component Φ hY₁ h2''
        have hYF := hfix _ ((MonoidHom.snd _ _).comp Φ.toMonoidHom) hΦ2 h2''
        refine sp_half_false hℓ hℓ2 he hK hB (by omega) hndP hndM hYF
          (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσk hs hN
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
          ← MonoidHom.range_eq_map]
        exact hρ₁c
      ·
        have h1'' : ∀ x ∈ Y.subgroupOf (symplecticOperatorCentralizer B (Agl : Module.End K V)),
            ((Φ.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1' _ (mem_map_of_mem _ hx)
        obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component (Φ.trans MulEquiv.prodComm) hY₁ h1''
        have hYF := hfix _ ((MonoidHom.fst _ _).comp Φ.toMonoidHom) hΦ1 h1''
        refine sp_half_false hℓ hℓ2 he hK hB (by omega) hndM hndP hYF
          (ρ₁.comp eY.symm.toMonoidHom) (hρ₁i.comp eY.symm.injective) ?_ σ hσk hs hN
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
          ← MonoidHom.range_eq_map]
        exact hρ₁c
    ·
      obtain ⟨-, -, hdP, -, -, -, e, -⟩ := hneg h1
      obtain ⟨bP⟩ : Nonempty (Basis (Fin r) K (eigenPlus l (Agl : Module.End K V))) :=
        ⟨Module.finBasisOfFinrankEq K _ hdP⟩
      exact gl_component_false hr hℓ hℓ2 he hK (((centralizerSimilitudeEquiv B Agl).trans e).trans
        (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)) hY₁ (σ.comp eY.toMonoidHom)
        hσ₁k hs
  · push Not at hsq
    obtain ⟨-, hF, hcard, hfinrank, bar, hbar, hpow, hbarbar, hpos, hneg⟩ := hnonsplit hsq
    let : Field (scalarSquareField (Agl : Module.End K V)) := hF.toField
    have hEodd : Odd (Nat.card (scalarSquareField (Agl : Module.End K V))) := by
      rw [hcard]
      exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
    have := finite_of_odd_card hEodd
    have : Module.Finite (scalarSquareField (Agl : Module.End K V)) V :=
      evaluationModule_finite (Agl : Module.End K V)
    rcases hε with h1 | h1
    ·
      obtain ⟨BE, -, hBEalt, hBEnd, ⟨m, hm⟩, hiff⟩ := hpos h1
      exact sp_component_false hℓ hℓ2 (j := 2 * e) (by omega)
        (by rw [hcard, ← pow_mul, mul_comm]) BE hBEalt hBEnd (by omega)
        (evaluationIsometryEquiv B Agl (isometryGroup BE)
          (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w) (mem_isometryGroup_iff BE) hiff)
        hY₁ (σ.comp eY.toMonoidHom) hσ₁k hs
    ·
      obtain ⟨h, -, hsymm, hsep, hiff⟩ := hneg h1
      let sigma := RingEquiv.ofBijective bar (Function.Involutive.bijective hbarbar)
      let h' : V →ₛₗ[sigma.toRingHom] V →ₗ[scalarSquareField (Agl : Module.End K V)]
        scalarSquareField (Agl : Module.End K V) := h
      have hnd' : h'.Nondegenerate :=
        ⟨hsep, fun y hy => hsep y fun x => by
          rw [← hsymm.eq x y]
          exact (congrArg bar (hy x)).trans (map_zero bar)⟩
      have hsigma : sigma ^ 2 = 1 := RingEquiv.ext hbarbar
      let s0 : scalarSquareField (Agl : Module.End K V) :=
        ⟨(Agl : Module.End K V), Algebra.self_mem_adjoin_singleton K _⟩
      have hs0 : (s0 : Module.End K V) = (0 : K) • 1 + (1 : K) • (Agl : Module.End K V) := by
        rw [zero_smul, zero_add, one_smul]
      have hbars : bar s0 = -s0 := by
        apply Subtype.ext
        rw [hbar s0 0 1 hs0, zero_smul, zero_sub, one_smul]
        rfl
      have hbarK : ∀ a : K, bar (algebraMap K (scalarSquareField (Agl : Module.End K V)) a) =
          algebraMap K (scalarSquareField (Agl : Module.End K V)) a := by
        intro a
        apply Subtype.ext
        rw [hbar _ a 0 (by rw [zero_smul, add_zero]; exact Algebra.algebraMap_eq_smul_one a),
          zero_smul, sub_zero]
        exact (Algebra.algebraMap_eq_smul_one a).symm
      have hne : sigma ≠ 1 := by
        intro heq
        have hfix : bar s0 = s0 := DFunLike.congr_fun heq s0
        rw [hbars] at hfix
        have hA : (Agl : Module.End K V) = -(Agl : Module.End K V) :=
          (congrArg Subtype.val hfix).symm
        have hA2 : (2 : K) • (Agl : Module.End K V) = 0 := by
          rw [two_smul]
          nth_rewrite 2 [hA]
          exact add_neg_cancel _
        apply hnonscalar 0
        rw [zero_smul]
        calc T.toLinearMap = (2 : K)⁻¹ • ((2 : K) • (Agl : Module.End K V)) := by
              rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
              rfl
          _ = 0 := by rw [hA2, smul_zero]
      have hs2 : s0 * s0 = algebraMap K (scalarSquareField (Agl : Module.End K V)) (d : K) := by
        apply Subtype.ext
        change (Agl : Module.End K V) * (Agl : Module.End K V) =
          algebraMap K (Module.End K V) (d : K)
        rw [hAA, Algebra.algebraMap_eq_smul_one]
      obtain ⟨a0, b0, hab0⟩ := exists_sq_add_sq hodd (-(d : K)⁻¹)
      have hab : ∃ a b : scalarSquareField (Agl : Module.End K V),
          sigma a = -a ∧ sigma b = -b ∧ a ^ 2 + b ^ 2 = -1 := by
        refine ⟨algebraMap K _ a0 * s0, algebraMap K _ b0 * s0, ?_, ?_, ?_⟩
        · change bar (algebraMap K _ a0 * s0) = _
          rw [map_mul, hbarK, hbars, mul_neg]
        · change bar (algebraMap K _ b0 * s0) = _
          rw [map_mul, hbarK, hbars, mul_neg]
        · have e1 : (algebraMap K _ a0 * s0) ^ 2 + (algebraMap K _ b0 * s0) ^ 2 =
              algebraMap K (scalarSquareField (Agl : Module.End K V)) (a0 ^ 2 + b0 ^ 2) *
                (s0 * s0) := by
            rw [map_add, map_pow, map_pow]
            ring
          rw [e1, hab0, hs2, ← map_mul, neg_mul, inv_mul_cancel₀ (Units.ne_zero d), map_neg,
            map_one]
      let Φ := evaluationIsometryEquiv B Agl (CatalogueBUnitaryIsometry.isometryGroup h')
        (fun φ => ∀ v w, h (φ v) (φ w) = h v w) (CatalogueBUnitaryIsometry.mem_isometryGroup_iff h')
        hiff
      exact unitary_component_false_of_quaternion_equiv hℓ hℓ2 he hcard (by omega) h' hsymm hnd'
        hsigma hne hpow hab Φ hY₁ (σ.comp eY.toMonoidHom) (hσs.comp eY.surjective) hσ₁k hs

end CFSG.ComponentClassification.OddClassSelector
