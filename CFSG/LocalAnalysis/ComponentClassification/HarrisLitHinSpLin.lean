module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpLinear

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module CFSG.ComponentClassification.RestrictedStd
open LinearMap (BilinForm)
open CFSG.ComponentClassification.OddClassSelector
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG (IsQuasisimple)

theorem false_of_block {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] {C Z : Subgroup G}
    (Φ : ↥C ≃* G₁ × G₂) {Y : Subgroup G} (hYC : Y ≤ C)
    (hY2 : ∀ y (hy : y ∈ Y), (Φ ⟨y, hYC hy⟩).2 = 1) (hq : IsQuasisimple G₂)
    (h2 : 2 ∣ Nat.card G₂) (hZ : ∀ g₂ : G₂, ((Φ.symm (1, g₂) : ↥C) : G) ∈ Z → g₂ = 1)
    (hU : ∀ N : Subgroup G, N ≤ C → (∀ g ∈ C, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → IsQuasisimple ↥N →
      N ⊓ Z = ⊥ → 2 ∣ Nat.card N → (∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) → False) : False := by
  set ψ : G₂ →* G := C.subtype.comp (Φ.symm.toMonoidHom.comp (MonoidHom.inr G₁ G₂)) with hψ
  have hψa : ∀ g₂, ψ g₂ = ((Φ.symm (1, g₂) : ↥C) : G) := fun _ => rfl
  have hψi : Function.Injective ψ := by
    intro a b hab
    rw [hψa, hψa] at hab
    have := Φ.symm.injective (Subtype.ext hab)
    exact (Prod.ext_iff.mp this).2
  refine hU ψ.range ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨g₂, rfl⟩
    exact (Φ.symm (1, g₂)).2
  · rintro g hg _ ⟨g₂, rfl⟩
    refine ⟨(Φ ⟨g, hg⟩).2 * g₂ * ((Φ ⟨g, hg⟩).2)⁻¹, ?_⟩
    rw [hψa, hψa]
    have : Φ.symm (1, (Φ ⟨g, hg⟩).2 * g₂ * ((Φ ⟨g, hg⟩).2)⁻¹) =
        ⟨g, hg⟩ * Φ.symm (1, g₂) * (⟨g, hg⟩ : ↥C)⁻¹ := by
      apply Φ.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      ext
      · simp
      · simp
    rw [this]
    rfl
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hψi) hq
  · rw [eq_bot_iff]
    rintro _ ⟨⟨g₂, rfl⟩, hz⟩
    rw [mem_bot, hZ g₂ (by rw [← hψa]; exact hz), map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv]
    exact h2
  · rintro _ ⟨g₂, rfl⟩ y hy
    rw [hψa]
    have : Φ.symm (1, g₂) * ⟨y, hYC hy⟩ = ⟨y, hYC hy⟩ * Φ.symm (1, g₂) := by
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      ext
      · simp
      · simp [hY2 y hy]
    exact congrArg Subtype.val this

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem false_of_half {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) {B : BilinForm K V} {W W' : Submodule K V}
    (hWalt : (B.domRestrict₁₂ W W).IsAlt) (hWnd : (B.domRestrict₁₂ W W).Nondegenerate)
    (hW'alt : (B.domRestrict₁₂ W' W').IsAlt) (hW'nd : (B.domRestrict₁₂ W' W').Nondegenerate)
    (hW0 : W ≠ ⊥) (hdim : 6 ≤ finrank K W + finrank K W') {C : Subgroup (isometryGroup B)}
    (Φ : ↥C ≃* isometryGroup (B.domRestrict₁₂ W W) × isometryGroup (B.domRestrict₁₂ W' W'))
    (hΦ1 : ∀ (g : ↥C) (x : W), (((Φ g).1.val x : W) : V) = (g : isometryGroup B).val x)
    {Y : Subgroup (isometryGroup B)} (hYC : Y ≤ C) (hY2 : ∀ x ∈ Y.subgroupOf C, (Φ x).2 = 1)
    (hY₁ : CFSG.IsComponent (Y.subgroupOf C)) {X' : Type} [Group X'] {X : Subgroup X'}
    (σ : Y →* X) (hσk : σ.ker ≤ center Y) (hs : SmallSource X)
    (hU : ∀ N : Subgroup (isometryGroup B), N ≤ C → (∀ g ∈ C, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      IsQuasisimple ↥N → N ⊓ scalarSigns B = ⊥ → 2 ∣ Nat.card N →
      (∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) → False) : False := by
  classical
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ he hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hℓ.odd_of_ne_two hℓ2).pow
  obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := restrict_component Φ hY₁ hY2
  let eY : Y.subgroupOf C ≃* Y := Subgroup.subgroupOfEquivOfLe hYC
  by_cases h4 : 4 ≤ finrank K W
  · set ρ := ρ₁.comp eY.symm.toMonoidHom with hρ
    have hρi : Function.Injective ρ := hρ₁i.comp eY.symm.injective
    have hρc : CFSG.IsComponent ρ.range := by
      rw [hρ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    let eρ := MonoidHom.ofInjective hρi
    exact sp_component_false hℓ hℓ2 he hK (B.domRestrict₁₂ W W) hWalt hWnd h4 (MulEquiv.refl _)
      hρc (σ.comp eρ.symm.toMonoidHom)
      (ker_comp_le_center eρ.symm.toMonoidHom eρ.symm.injective σ hσk) hs
  ·
    have hWpos : 0 < finrank K W :=
      Nat.pos_of_ne_zero fun h => hW0 (Submodule.finrank_eq_zero.mp h)
    obtain ⟨k, hk⟩ := even_finrank (B.domRestrict₁₂ W W) hWalt hWnd
    have h4' : 4 ≤ finrank K W' := by omega
    have hW'0 : W' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at h4'
      omega
    have hq := isometry_quasisimple_of_four_le (B.domRestrict₁₂ W' W') hW'alt hW'nd h4' hodd
    have hneg1 : negIsometry (B.domRestrict₁₂ W' W') ≠ 1 := by
      intro h
      rw [Submodule.ne_bot_iff] at hW'0
      obtain ⟨x, hx, hx0⟩ := hW'0
      have := congrArg (fun g : isometryGroup (B.domRestrict₁₂ W' W') =>
        ((g.val ⟨x, hx⟩ : W') : V)) h
      simp only [negIsometry_apply, Submodule.coe_neg, OneMemClass.coe_one] at this
      exact hx0 (by
        have h' : (2 : K) • x = 0 := by
          rw [two_smul]
          nth_rewrite 1 [← neg_neg x]
          rw [this]
          exact neg_add_cancel x
        exact (smul_eq_zero.mp h').resolve_left h2)
    have h2c : 2 ∣ Nat.card (isometryGroup (B.domRestrict₁₂ W' W')) := by
      have ho : orderOf (negIsometry (B.domRestrict₁₂ W' W')) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact negIsometry_mul_self _) hneg1
      rw [← ho]
      exact orderOf_dvd_natCard _
    refine false_of_block Φ hYC (fun y hy => hY2 _ (mem_subgroupOf.mpr hy)) hq h2c
      (fun g₂ hz => ?_) hU
    set c := Φ.symm (1, g₂) with hc
    have hcW : ∀ x : W, (c : isometryGroup B).val x = x := by
      intro x
      rw [← hΦ1 c x, hc, MulEquiv.apply_symm_apply]
      rfl
    rcases (mem_scalarSigns_iff B _).mp hz with h1 | h1
    · have : c = 1 := Subtype.ext h1
      have h' := congrArg Φ this
      rw [hc, MulEquiv.apply_symm_apply, map_one] at h'
      exact (Prod.ext_iff.mp h').2
    · exfalso
      rw [Submodule.ne_bot_iff] at hW0
      obtain ⟨x, hx, hx0⟩ := hW0
      have h3 := hcW ⟨x, hx⟩
      rw [h1, negIsometry_apply] at h3
      have h3' : -x = x := h3
      apply hx0
      have h' : (2 : K) • x = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h3']
        exact neg_add_cancel x
      exact (smul_eq_zero.mp h').resolve_left h2

theorem sp_linear_false_of_noComm {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) {r : ℕ} (hr : 3 ≤ r) (hdim : finrank K V = 2 * r)
    {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (T : V ≃ₗ[K] V) (d μ : Kˣ) (hsquare : ∀ x, T (T x) = (d : K) • x)
    (hsim : ∀ x y, B (T x) (T y) = (μ : K) * B x y)
    (hnonscalar : ∀ c : K, T.toLinearMap ≠ c • (1 : Module.End K V))
    {Y : Subgroup (isometryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (symplecticOperatorCentralizer B T.toLinearMap))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hs : SmallSource X)
    (hU : ∀ N : Subgroup (isometryGroup B), N ≤ symplecticOperatorCentralizer B T.toLinearMap →
      (∀ g ∈ symplecticOperatorCentralizer B T.toLinearMap, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      IsQuasisimple ↥N → N ⊓ scalarSigns B = ⊥ → 2 ∣ Nat.card N →
      (∀ n ∈ N, ∀ y ∈ Y, n * y = y * n) → False) :
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
      obtain ⟨-, haltP, haltM, hndP, hndM, e, he'⟩ := hpos h1
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
      rcases CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
          (isComponent_map_of_isComponent Φ hY₁) with h2' | h1'
      ·
        exact false_of_half hℓ hℓ2 he hK haltP hndP haltM hndM hP (by omega) Φ hΦ1 hY'.1
          (fun x hx => h2' _ (mem_map_of_mem _ hx)) hY₁ σ hσk hs hU
      ·
        exact false_of_half hℓ hℓ2 he hK haltM hndM haltP hndP hM (by omega)
          (Φ.trans MulEquiv.prodComm) hΦ2 hY'.1 (fun x hx => h1' _ (mem_map_of_mem _ hx)) hY₁ σ
          hσk hs hU
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

end CFSG.ComponentClassification.HarrisLit.Hin
