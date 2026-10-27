module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz8

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz8

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open Matrix

set_option linter.unusedSectionVars false

section HeisSix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_linearEquiv_plane_u62 (hK : Nat.card K = 4) {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hW : Module.finrank K W = 2) : Nat.card (W ≃ₗ[K] W) = 180 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have e : W ≃ₗ[K] (Fin 2 → K) := LinearEquiv.ofFinrankEq W (Fin 2 → K) (by simp [hW])
  have h1 : Nat.card (W ≃ₗ[K] W) = Nat.card ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    Nat.card_congr
      { toFun := fun g => e.symm.trans (g.trans e)
        invFun := fun g => e.trans (g.trans e.symm)
        left_inv := fun g => by ext; simp
        right_inv := fun g => by ext; simp }
  rw [h1, ← Nat.card_congr (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K).toEquiv,
    Matrix.card_GL_field, Fin.prod_univ_two]
  have hK' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [hK']
  norm_num

theorem commute_of_pow_three_u62 (hK : Nat.card K = 4) {P : Subgroup (GL (Fin 6) K)}
    (hP3 : ∃ k : ℕ, Nat.card P = 3 ^ k) (hcard : 243 ≤ Nat.card P)
    (hcomm : ∀ g ∈ P, ∀ g' ∈ P, ∃ c : Kˣ,
      g * g' = GeneralLinearGroup.scalar (Fin 6) c * (g' * g))
    {x y : GL (Fin 6) K} (hx : x ∈ P) (hy : y ∈ P) (hy3 : y ^ 3 = 1) : x * y = y * x := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  by_contra hxy
  set sc : Kˣ →* GL (Fin 6) K := GeneralLinearGroup.scalar (Fin 6) with hsc
  have hsinj : Function.Injective sc :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.scalar_injective (by norm_num)
  have hscc : ∀ (a : Kˣ) (g : GL (Fin 6) K), g * sc a = sc a * g := fun a g =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar a g).eq
  obtain ⟨c, hc⟩ := hcomm x hx y hy
  have hKu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hc3 : c ^ 3 = 1 := by rw [← hKu]; exact pow_card_eq_one'
  have hc1 : c ≠ 1 := fun h1 => hxy (by rw [hc, h1, map_one, one_mul])
  choose κ hκ using fun g z : ↥P => hcomm g g.2 z z.2
  let κh : ↥P → ↥P →* Kˣ := fun z =>
    { toFun := fun g => κ g z
      map_one' := by
        apply hsinj
        have h1 := hκ 1 z
        rw [OneMemClass.coe_one, one_mul, mul_one] at h1
        have h2 : sc (κ 1 z) * (z : GL (Fin 6) K) = 1 * z := by rw [← h1, one_mul]
        rw [mul_right_cancel h2, map_one]
      map_mul' := fun g g' => by
        apply hsinj
        have h1 := hκ (g * g') z
        have h2 := hκ g z
        have h3 := hκ g' z
        rw [Subgroup.coe_mul] at h1
        have e : sc (κ (g * g') z) * ((z : GL (Fin 6) K) * (g * g')) =
            sc (κ g z * κ g' z) * ((z : GL (Fin 6) K) * (g * g')) := by
          rw [← h1, map_mul]
          calc (g : GL (Fin 6) K) * g' * z = g * (g' * z) := by group
            _ = g * (sc (κ g' z) * (z * g')) := by rw [h3]
            _ = sc (κ g' z) * ((g : GL (Fin 6) K) * z * g') := by
                rw [← mul_assoc, hscc, mul_assoc, mul_assoc]
            _ = sc (κ g' z) * (sc (κ g z) * (z * g) * g') := by rw [h2]
            _ = sc (κ g z) * sc (κ g' z) * (z * (g * g')) := by
                rw [← mul_assoc, ← mul_assoc, hscc (κ g z) (sc (κ g' z))]
                group
        exact mul_right_cancel e }
  let φ : ↥P →* Kˣ × Kˣ := (κh ⟨x, hx⟩).prod (κh ⟨y, hy⟩)
  have hker27 : 27 ≤ Nat.card φ.ker := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card (Set.range φ) ≤ 9 := by
      have := Finite.card_subtype_le (fun z : Kˣ × Kˣ => z ∈ Set.range φ)
      rw [Nat.card_prod, hKu] at this
      exact this
    have : 243 ≤ Nat.card φ.ker * 9 := hcard.trans (h1 ▸ Nat.mul_le_mul_left _ h2)
    omega
  have hkercomm : ∀ g : ↥P, g ∈ φ.ker → (g : GL (Fin 6) K) * x = x * g ∧ (g : GL (Fin 6) K) * y = y * g := by
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hg
    have h1 := hκ g ⟨x, hx⟩
    have h2 := hκ g ⟨y, hy⟩
    have e1 : κ g ⟨x, hx⟩ = 1 := hg.1
    have e2 : κ g ⟨y, hy⟩ = 1 := hg.2
    rw [e1, map_one, one_mul] at h1
    rw [e2, map_one, one_mul] at h2
    exact ⟨h1, h2⟩
  set X : Matrix (Fin 6) (Fin 6) K := (x : Matrix (Fin 6) (Fin 6) K) with hXdef
  set Xi : Matrix (Fin 6) (Fin 6) K := ((x⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hXidef
  set Y : Matrix (Fin 6) (Fin 6) K := (y : Matrix (Fin 6) (Fin 6) K) with hYdef
  set ζ : K := (c : K) with hζdef
  have hXXi : X * Xi = 1 := by rw [hXdef, hXidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXiX : Xi * X = 1 := by rw [hXdef, hXidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXY : X * Y = ζ • (Y * X) := by
    rw [hXdef, hYdef, ← Units.val_mul, hc,
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.coe_scalar_mul, Units.val_mul]
  have hY3 : Y * Y * Y = 1 := by
    rw [hYdef, ← Units.val_mul, ← Units.val_mul, ← pow_three', hy3, Units.val_one]
  have hζ3 : ζ ^ 3 = 1 := by rw [hζdef, ← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hζ1 : ζ ≠ 1 := fun h1 => hc1 (Units.ext h1)
  have hζ0 : ζ ≠ 0 := c.ne_zero
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    have : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ1)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h2
    apply hζ1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hζ3, h2, inv_one, one_mul]
  have h3 : (3 : K) = 1 := by
    have : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination this
  have hYX : Y * X = ζ ^ 2 • (X * Y) := by
    rw [hXY, smul_smul, show ζ ^ 2 * ζ = ζ ^ 3 by ring, hζ3, one_smul]
  have hYXi : Y * Xi = ζ • (Xi * Y) := by
    have e : Xi * (X * Y) * Xi = Xi * (ζ • (Y * X)) * Xi := by rw [hXY]
    rw [← mul_assoc, hXiX, one_mul, Matrix.mul_smul, Matrix.smul_mul, mul_assoc, mul_assoc, hXXi,
      mul_one] at e
    exact e
  have hXmap : ∀ (μ : K) (v : Fin 6 → K), Y *ᵥ v = μ • v → Y *ᵥ (X *ᵥ v) = (ζ ^ 2 * μ) • (X *ᵥ v) := by
    intro μ v hv
    rw [Matrix.mulVec_mulVec, hYX, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
      smul_smul]
  have hXimap : ∀ (μ : K) (v : Fin 6 → K), Y *ᵥ v = μ • v →
      Y *ᵥ (Xi *ᵥ v) = (ζ * μ) • (Xi *ᵥ v) := by
    intro μ v hv
    rw [Matrix.mulVec_mulVec, hYXi, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
      smul_smul]
  let E : K → Submodule K (Fin 6 → K) := fun μ => Module.End.eigenspace (Matrix.toLin' Y) μ
  have hmemE : ∀ μ v, v ∈ E μ ↔ Y *ᵥ v = μ • v := fun μ v => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hYY : ∀ w : Fin 6 → K, Y *ᵥ (Y *ᵥ (Y *ᵥ w)) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hY3, Matrix.one_mulVec]
  have hdec : ∀ w : Fin 6 → K,
      (w + Y *ᵥ w + Y *ᵥ (Y *ᵥ w)) ∈ E 1 ∧
      (w + ζ • (Y *ᵥ w) + ζ ^ 2 • (Y *ᵥ (Y *ᵥ w))) ∈ E (ζ ^ 2) ∧
      (w + ζ ^ 2 • (Y *ᵥ w) + ζ • (Y *ᵥ (Y *ᵥ w))) ∈ E ζ ∧
      w = (w + Y *ᵥ w + Y *ᵥ (Y *ᵥ w)) + (w + ζ • (Y *ᵥ w) + ζ ^ 2 • (Y *ᵥ (Y *ᵥ w))) +
        (w + ζ ^ 2 • (Y *ᵥ w) + ζ • (Y *ᵥ (Y *ᵥ w))) := by
    intro w
    refine ⟨(hmemE _ _).2 ?_, (hmemE _ _).2 ?_, (hmemE _ _).2 ?_, ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_add, hYY, one_smul]
      abel
    · rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hYY,
        smul_add, smul_add, smul_smul, smul_smul, show ζ ^ 2 * ζ = 1 by rw [← hζ3]; ring,
        show ζ ^ 2 * ζ ^ 2 = ζ by linear_combination ζ * hζ3, one_smul]
      abel
    · rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hYY,
        smul_add, smul_add, smul_smul, smul_smul, show ζ * ζ ^ 2 = 1 by rw [← hζ3]; ring,
        show ζ * ζ = ζ ^ 2 by ring, one_smul]
      abel
    · have e1 : (1 + ζ + ζ ^ 2) • (Y *ᵥ w) = 0 := by
        rw [show 1 + ζ + ζ ^ 2 = ζ ^ 2 + ζ + 1 by ring, hζ, zero_smul]
      have e2 : (1 + ζ ^ 2 + ζ) • (Y *ᵥ (Y *ᵥ w)) = 0 := by
        rw [show 1 + ζ ^ 2 + ζ = ζ ^ 2 + ζ + 1 by ring, hζ, zero_smul]
      have e3 : (3 : K) • w = w := by rw [h3, one_smul]
      rw [add_smul, add_smul, one_smul] at e1 e2
      rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul] at e3
      linear_combination (norm := module) -e1 - e2 - e3
  have hfin : ∀ μ : K, Module.finrank K (E μ) ≤ Module.finrank K (E (ζ ^ 2 * μ)) := by
    intro μ
    let f : E μ →ₗ[K] E (ζ ^ 2 * μ) := (Matrix.toLin' X).restrict (fun v hv => by
      rw [hmemE] at hv ⊢
      rw [Matrix.toLin'_apply]
      exact hXmap μ v hv)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun a b hab => ?_
    apply Subtype.ext
    have h1 : X *ᵥ (a : Fin 6 → K) = X *ᵥ (b : Fin 6 → K) := congrArg Subtype.val hab
    have h2 := congrArg (fun v => Xi *ᵥ v) h1
    simpa only [Matrix.mulVec_mulVec, hXiX, Matrix.one_mulVec] using h2
  have hζ4 : ζ ^ 2 * ζ ^ 2 = ζ := by linear_combination ζ * hζ3
  have hζ5 : ζ ^ 2 * ζ = 1 := by linear_combination hζ3
  have hd1 := hfin 1
  have hd2 := hfin (ζ ^ 2)
  have hd3 := hfin ζ
  rw [mul_one] at hd1
  rw [hζ4] at hd2
  rw [hζ5] at hd3
  have htop : (⊤ : Submodule K (Fin 6 → K)) ≤ E 1 ⊔ E (ζ ^ 2) ⊔ E ζ := by
    intro w _
    obtain ⟨h0, h1, h2, hw⟩ := hdec w
    rw [hw]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left h0))
      (Submodule.mem_sup_left (Submodule.mem_sup_right h1))) (Submodule.mem_sup_right h2)
  have h6 : Module.finrank K (⊤ : Submodule K (Fin 6 → K)) = 6 := by
    rw [finrank_top, Module.finrank_fin_fun]
  have hge : 6 ≤ 3 * Module.finrank K (E 1) := by
    have e1 := Submodule.finrank_mono htop
    have e2 := Submodule.finrank_add_le_finrank_add_finrank (E 1 ⊔ E (ζ ^ 2)) (E ζ)
    have e3 := Submodule.finrank_add_le_finrank_add_finrank (E 1) (E (ζ ^ 2))
    omega
  have hd01 : E 1 ⊓ E (ζ ^ 2) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨h1, h2⟩
    have h1' := (hmemE 1 v).1 h1
    have h2' := (hmemE (ζ ^ 2) v).1 h2
    have e : (1 - ζ ^ 2) • v = 0 := by rw [sub_smul, ← h1', ← h2', sub_self]
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.1 e).resolve_left (sub_ne_zero.2 (Ne.symm hζ2))
  have hd012 : (E 1 ⊔ E (ζ ^ 2)) ⊓ E ζ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, h3⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have ha' := (hmemE _ _).1 ha
    have hb' := (hmemE _ _).1 hb
    have h3' := (hmemE ζ (a + b)).1 h3
    rw [Matrix.mulVec_add, ha', hb'] at h3'
    have e : (1 - ζ) • a = (ζ - ζ ^ 2) • b := by
      rw [sub_smul, sub_smul, one_smul]
      linear_combination (norm := module) h3'
    have hu1 : (1 - ζ) • a ∈ E 1 := Submodule.smul_mem _ _ ha
    have hu2 : (1 - ζ) • a ∈ E (ζ ^ 2) := e ▸ Submodule.smul_mem _ _ hb
    have hu : (1 - ζ) • a = 0 := by
      have : (1 - ζ) • a ∈ E 1 ⊓ E (ζ ^ 2) := ⟨hu1, hu2⟩
      rwa [hd01, Submodule.mem_bot] at this
    have ha0 : a = 0 := (smul_eq_zero.1 hu).resolve_left (sub_ne_zero.2 (Ne.symm hζ1))
    have hb0 : b = 0 := by
      rw [hu] at e
      have hne : ζ - ζ ^ 2 ≠ 0 := by
        rw [show ζ - ζ ^ 2 = ζ * (1 - ζ) by ring]
        exact mul_ne_zero hζ0 (sub_ne_zero.2 (Ne.symm hζ1))
      exact (smul_eq_zero.1 e.symm).resolve_left hne
    rw [ha0, hb0, add_zero, Submodule.mem_bot]
  have hle : 3 * Module.finrank K (E 1) ≤ 6 := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (E 1) (E (ζ ^ 2))
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq (E 1 ⊔ E (ζ ^ 2)) (E ζ)
    rw [hd01, finrank_bot] at e1
    rw [hd012, finrank_bot] at e2
    have e3 := Submodule.finrank_le (E 1 ⊔ E (ζ ^ 2) ⊔ E ζ)
    rw [Module.finrank_fin_fun] at e3
    omega
  have hdim : Module.finrank K (E 1) = 2 := by omega
  have hGY : ∀ g : ↥φ.ker, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * Y =
      Y * ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := fun g => by
    rw [hYdef, ← Units.val_mul, ← Units.val_mul, (hkercomm g g.2).2]
  have hGX : ∀ g : ↥φ.ker, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * X =
      X * ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := fun g => by
    rw [hXdef, ← Units.val_mul, ← Units.val_mul, (hkercomm g g.2).1]
  have hmaps : ∀ g : ↥φ.ker, ∀ v ∈ E 1,
      Matrix.toLin' ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) v ∈ E 1 := by
    intro g v hv
    rw [hmemE] at hv ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hGY, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  let Rh : ↥φ.ker →* Module.End K (E 1) :=
    { toFun := fun g => (Matrix.toLin' ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)).restrict (hmaps g)
      map_one' := by
        refine LinearMap.ext fun v => Subtype.ext ?_
        rw [LinearMap.restrict_coe_apply, OneMemClass.coe_one, OneMemClass.coe_one, Units.val_one,
          Matrix.toLin'_one]
        rfl
      map_mul' := fun g g' => by
        refine LinearMap.ext fun v => Subtype.ext ?_
        rw [LinearMap.restrict_coe_apply, Module.End.mul_apply, LinearMap.restrict_coe_apply,
          LinearMap.restrict_coe_apply, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
          Matrix.toLin'_mul]
        rfl }
  have hfaith : ∀ g : ↥φ.ker, Rh g = 1 → g = 1 := by
    intro g hg
    set G : Matrix (Fin 6) (Fin 6) K := ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hGdef
    have hfix : ∀ v ∈ E 1, G *ᵥ v = v := by
      intro v hv
      have := congrArg (fun f : Module.End K (E 1) => ((f ⟨v, hv⟩ : E 1) : Fin 6 → K)) hg
      simp only [Rh, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.restrict_coe_apply, Module.End.one_apply,
        Matrix.toLin'_apply] at this
      exact this
    have hGXv : ∀ w, G *ᵥ (X *ᵥ w) = X *ᵥ (G *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hGX, ← Matrix.mulVec_mulVec]
    have hall : ∀ w, G *ᵥ w = w := by
      intro w
      obtain ⟨h0, h1, h2, hw⟩ := hdec w
      set p₀ := w + Y *ᵥ w + Y *ᵥ (Y *ᵥ w)
      set p₁ := w + ζ • (Y *ᵥ w) + ζ ^ 2 • (Y *ᵥ (Y *ᵥ w))
      set p₂ := w + ζ ^ 2 • (Y *ᵥ w) + ζ • (Y *ᵥ (Y *ᵥ w))
      have hp₁ : G *ᵥ p₁ = p₁ := by
        have hu : Xi *ᵥ p₁ ∈ E 1 := by
          rw [hmemE]
          have := hXimap _ _ ((hmemE _ _).1 h1)
          rwa [show ζ * ζ ^ 2 = 1 by linear_combination hζ3] at this
        have hp : p₁ = X *ᵥ (Xi *ᵥ p₁) := by rw [Matrix.mulVec_mulVec, hXXi, Matrix.one_mulVec]
        rw [hp, hGXv, hfix _ hu]
      have hp₂ : G *ᵥ p₂ = p₂ := by
        have hu1 : Y *ᵥ (Xi *ᵥ p₂) = ζ ^ 2 • (Xi *ᵥ p₂) := by
          have := hXimap _ _ ((hmemE _ _).1 h2)
          rwa [show ζ * ζ = ζ ^ 2 by ring] at this
        have hu : Xi *ᵥ (Xi *ᵥ p₂) ∈ E 1 := by
          rw [hmemE]
          have := hXimap _ _ hu1
          rwa [show ζ * ζ ^ 2 = 1 by linear_combination hζ3] at this
        have hp : p₂ = X *ᵥ (X *ᵥ (Xi *ᵥ (Xi *ᵥ p₂))) := by
          have hXX : X * X * Xi * Xi = 1 := by
            rw [Matrix.mul_assoc X X Xi, hXXi, Matrix.mul_one, hXXi]
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
        rw [hp, hGXv, hGXv, hfix _ hu]
      rw [hw, Matrix.mulVec_add, Matrix.mulVec_add, hfix _ h0, hp₁, hp₂]
    have hG1 : G = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun w => ?_
      rw [Matrix.toLin'_apply, hall, Matrix.toLin'_one, LinearMap.id_apply]
    apply Subtype.ext
    apply Subtype.ext
    exact Units.ext hG1
  let ρ : ↥φ.ker →* (Module.End K (E 1))ˣ := Rh.toHomUnits
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_bot]
    exact hfaith g (by
      have := congrArg Units.val hg
      simpa [ρ] using this)
  have hdvd : Nat.card ↥φ.ker ∣ 180 := by
    have h1 := Subgroup.card_dvd_of_injective ρ hρ
    have h2 : Nat.card (Module.End K (E 1))ˣ = 180 := by
      rw [← card_linearEquiv_plane_u62 hK hdim]
      exact Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv K (E 1)).toEquiv
    rwa [h2] at h1
  obtain ⟨k, hk⟩ := hP3
  have hdvdP : Nat.card ↥φ.ker ∣ 3 ^ k := hk ▸ Subgroup.card_subgroup_dvd_card φ.ker
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvdP
  rw [hj] at hker27 hdvd
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : 27 ∣ 180 := (show 27 = 3 ^ 3 by norm_num) ▸ (Nat.pow_dvd_pow 3 hj3).trans hdvd
  norm_num at h27

theorem commute_of_cube_u62 (hK : Nat.card K = 4) {P : Subgroup (GL (Fin 6) K)}
    (hP3 : ∃ k : ℕ, Nat.card P = 3 ^ k) (hcard : 243 ≤ Nat.card P)
    (hcube : ∀ g ∈ P, ∃ c : Kˣ, g ^ 3 = GeneralLinearGroup.scalar (Fin 6) c)
    (hcomm : ∀ g ∈ P, ∀ g' ∈ P, ∃ c : Kˣ,
      g * g' = GeneralLinearGroup.scalar (Fin 6) c * (g' * g))
    {x y : GL (Fin 6) K} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  classical
  have hsinj : Function.Injective (GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.scalar_injective (by norm_num)
  have hcs : ∀ g : ↥P, ∃ c : Kˣ, (g : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c :=
    fun g => hcube g g.2
  have hmul3 : ∀ g ∈ P, ∀ g' ∈ P, (g * g') ^ 3 = g ^ 3 * g' ^ 3 := fun g hg g' hg' => by
    obtain ⟨c, hc⟩ := hcomm g hg g' hg'
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.cube_mul_of_comm
      (by norm_num) hc (hcube g' hg')
  let ψ : ↥P →* Kˣ :=
    { toFun := fun g => (hcs g).choose
      map_one' := hsinj (by rw [← (hcs 1).choose_spec, Subgroup.coe_one, one_pow, map_one])
      map_mul' := fun g g' => hsinj (by
        rw [map_mul, ← (hcs g).choose_spec, ← (hcs g').choose_spec, ← (hcs (g * g')).choose_spec,
          Subgroup.coe_mul, hmul3 g g.2 g' g'.2]) }
  have hker : ψ.ker ≤ Subgroup.center ↥P := by
    intro g hg
    have hg1 : (hcs g).choose = 1 := hg
    have hg3 : (g : GL (Fin 6) K) ^ 3 = 1 := by rw [(hcs g).choose_spec, hg1, map_one]
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (commute_of_pow_three_u62 hK hP3 hcard hcomm z.2 g.2 hg3)
  exact congrArg Subtype.val (commutative_of_cyclic_center_quotient ψ hker ⟨x, hx⟩ ⟨y, hy⟩)

end HeisSix

section StarSix

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem exists_star_three_u62 (h : UnitaryFieldData p f K) (hp : p = 2) (hf : f = 1) (hn : n = 6)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (hD : IsElemAbelian 3 D) (hD81 : 81 ≤ Nat.card D) :
    ∃ E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))), E ≤ D ∧
      Nat.card D ≤ 3 * Nat.card E ∧
      ∃ U : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), U ≠ ⊥ ∧
        IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  subst hp hf hn
  classical
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  haveI : Finite (GL (Fin 6) K) := inferInstance
  have hK4 : Nat.card K = 4 := h.card.trans (by norm_num)
  have hn3 : 3 ≤ 6 := by norm_num
  have hq : ¬(6 = 3 ∧ 2 ^ 1 = 2) := by omega
  have hsinj : Function.Injective (GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K) :=
    scalar_injective (by norm_num)
  have hKu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK4]
  have hu3 : ∀ z : Kˣ, z ^ 3 = 1 := fun z => by rw [← hKu]; exact pow_card_eq_one'
  have hDle : D ≤ primeFormD h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    intro β hβ
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hq, MonoidHom.mem_ker]
    set θ := primeFormFieldFactor h isPrimeFormGram_one hn3 hq β
    have hcard : Nat.card (RingAut K) = 2 :=
      (card_ringAut_and_isCyclic Nat.prime_two K (h.card.trans (by norm_num))).1
    haveI : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have h2 : θ ^ 2 = 1 := by
      have := pow_card_eq_one' (G := RingAut K) (x := θ)
      rwa [hcard] at this
    have h3 : θ ^ 3 = 1 := by rw [← map_pow, hD.2 β hβ, map_one]
    calc θ = θ ^ 3 * (θ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, one_mul, inv_one]
  set U := primeFormUnitary h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hUdef
  set c := primeFormConjHom h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hcdef
  set PU : Subgroup ↥U := D.comap c with hPUdef
  set P : Subgroup (GL (Fin 6) K) := PU.map U.subtype with hPdef
  have hPU : P ≤ U := Subgroup.map_subtype_le PU
  have hmemP : ∀ A : ↥U, (A : GL (Fin 6) K) ∈ P ↔ c A ∈ D := fun A =>
    ⟨fun ⟨B, hB, hBA⟩ => by rw [← Subtype.ext hBA]; exact hB, fun hA => ⟨A, hA, rfl⟩⟩
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hnorm : ∀ z : Kˣ, h.norm (z : K) = 1 := by
    intro z
    rw [h.norm_eq_pow, show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hsc : ∀ z : Kˣ, GeneralLinearGroup.scalar (Fin 6) z ∈ U := fun z =>
    scalar_mem_primeFormUnitary h (hnorm z)
  have hsc1 : ∀ z : Kˣ, c ⟨_, hsc z⟩ = 1 := fun z =>
    CFSG.RankThree.Classical.primeFormConjHom_scalar h 6 z (hsc z)
  have hscD : ∀ z : Kˣ, c ⟨_, hsc z⟩ ∈ D := fun z => by rw [hsc1 z]; exact one_mem D
  have hZ : ∀ z : Kˣ, h.norm (z : K) = 1 → GeneralLinearGroup.scalar (Fin 6) z ∈ P :=
    fun z _ => (hmemP ⟨_, hsc z⟩).2 (hscD z)
  have hcube : ∀ g ∈ P, ∃ z : Kˣ, g ^ 3 = GeneralLinearGroup.scalar (Fin 6) z := by
    rintro _ ⟨A, hA, rfl⟩
    have h1 : c (A ^ 3) = 1 := by rw [map_pow]; exact hD.2 _ hA
    obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn3 h1
    exact ⟨z, by rw [← hz]; rfl⟩
  have hcomm : ∀ g ∈ P, ∀ g' ∈ P, ∃ z : Kˣ,
      g * g' = GeneralLinearGroup.scalar (Fin 6) z * (g' * g) := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    have h1 : c (A * B * A⁻¹ * B⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hDcomm _ hA _ hB]
      group
    obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn3 h1
    refine ⟨z, ?_⟩
    have hz' : (A : GL (Fin 6) K) * B * (A : GL (Fin 6) K)⁻¹ * (B : GL (Fin 6) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 6) z := hz
    calc (A : GL (Fin 6) K) * B = ((A : GL (Fin 6) K) * B * (A : GL (Fin 6) K)⁻¹ *
          (B : GL (Fin 6) K)⁻¹) * (B * A) := by group
      _ = GeneralLinearGroup.scalar (Fin 6) z * (B * A) := by rw [hz']
  have hP3 : ∃ k : ℕ, Nat.card P = 3 ^ k := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpg : IsPGroup 3 P := by
      intro g
      obtain ⟨z, hz⟩ := hcube g g.2
      refine ⟨2, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one, show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, hz, ← map_pow,
        hu3, map_one]
    exact hpg.exists_card_eq
  let fP : ↥PU →* ↥D := (c.comp PU.subtype).codRestrict D (fun x => x.2)
  have hfP : Function.Surjective fP := by
    rintro ⟨α, hα⟩
    obtain ⟨A, hA⟩ := hDle hα
    exact ⟨⟨A, show c A ∈ D by rw [hA]; exact hα⟩, Subtype.ext hA⟩
  have hcardPU : Nat.card PU = Nat.card P := by
    rw [hPdef, Subgroup.card_map_of_injective U.subtype_injective]
  have hscK : ∀ z : Kˣ, (⟨⟨_, hsc z⟩, hscD z⟩ : ↥PU) ∈ fP.ker := fun z => by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (hsc1 z)
  have hker3 : 3 ≤ Nat.card fP.ker := by
    have hinj : Function.Injective (fun z : Kˣ => (⟨_, hscK z⟩ : ↥fP.ker)) := by
      intro z z' hzz
      exact hsinj (congrArg (fun w : ↥fP.ker => (((w : ↥PU) : ↥U) : GL (Fin 6) K)) hzz)
    have := Nat.card_le_card_of_injective _ hinj
    rwa [hKu] at this
  have hcard : 243 ≤ Nat.card P := by
    have h1 := Subgroup.card_mul_index fP.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hfP, Subgroup.card_top, hcardPU] at h1
    rw [← h1]
    calc 243 = 3 * 81 := by norm_num
      _ ≤ Nat.card fP.ker * Nat.card D := Nat.mul_le_mul hker3 hD81
  obtain ⟨EG, hEGP, hcardE, t, htSU, ht2, htns, htc⟩ :=
    Claims1310r.exists_centralized_involution_three h (by norm_num) (by norm_num) P hPU hZ hcube hcomm
  have hcardEG : Nat.card P ≤ 3 * Nat.card EG := hcardE.resolve_right (by
    rintro ⟨x, hx, y, hy, hxy⟩
    exact hxy (commute_of_cube_u62 hK4 hP3 hcard hcube hcomm (hEGP hx) (hEGP hy)))
  set EU : Subgroup ↥U := EG.comap U.subtype with hEUdef
  have hEUPU : EU ≤ PU := fun x hx => (hmemP x).1 (hEGP hx)
  set E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) :=
    EU.map c with hEdef
  have hED : E ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hEUPU hx
  set tP : primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
    ((⟨t, htSU⟩ : gramSU h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
      primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) with htPdef
  have htP2 : tP ^ 2 = 1 := by
    rw [htPdef, ← QuotientGroup.mk_pow]
    have : (⟨t, htSU⟩ : gramSU h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ht2)
    rw [this, QuotientGroup.mk_one]
  have htP1 : tP ≠ 1 := by
    intro h1
    rw [htPdef, QuotientGroup.eq_one_iff] at h1
    obtain ⟨z, -, -, hz⟩ := h1
    exact htns z hz
  have hEfix : ∀ φ ∈ E, φ tP = tP := by
    rintro _ ⟨x, hx, rfl⟩
    rw [htPdef, hcdef, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change (x : GL (Fin 6) K) * t * (x : GL (Fin 6) K)⁻¹ = t
    rw [htc (x : GL (Fin 6) K) hx, mul_inv_cancel_right]
  refine ⟨E, hED, ?_, Subgroup.zpowers tP, ?_, ?_, ?_⟩
  ·
    have hmap : (EU.subgroupOf PU).map fP = E.subgroupOf D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.2 ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.1 hx
        exact ⟨⟨y, hEUPU hy⟩, Subgroup.mem_subgroupOf.2 hy, Subtype.ext hyx⟩
    have hEGU : EG ≤ U := hEGP.trans hPU
    have hmapEU : EU.map U.subtype = EG :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hEGU)
    have hcardEU : Nat.card (EU.subgroupOf PU) = Nat.card EG := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEUPU).toEquiv, ← hmapEU,
        Subgroup.card_map_of_injective U.subtype_injective]
    have hidxEU : (EU.subgroupOf PU).index ≤ 3 := by
      have h1 := Subgroup.card_mul_index (EU.subgroupOf PU)
      rw [hcardEU, hcardPU] at h1
      have hpos : 0 < Nat.card EG := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : 4 * Nat.card EG ≤ (EU.subgroupOf PU).index * Nat.card EG :=
        Nat.mul_le_mul_right _ hlt
      rw [mul_comm (EU.subgroupOf PU).index, h1] at this
      omega
    have hdvd := Subgroup.index_map_dvd (H := EU.subgroupOf PU) hfP
    rw [hmap] at hdvd
    have hne : (EU.subgroupOf PU).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hrel : E.relIndex D ≤ 3 := (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hidxEU
    have h2 := Subgroup.relIndex_mul_card E D
    rw [inf_of_le_left hED] at h2
    rw [← h2]
    exact Nat.mul_le_mul_right _ hrel
  · intro hbot
    apply htP1
    have : tP ∈ Subgroup.zpowers tP := Subgroup.mem_zpowers tP
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · intro u
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 u.2
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, htP2, _root_.one_zpow, Subgroup.coe_one]
  · intro φ hφ u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [map_zpow, hEfix φ hφ]
    exact Subgroup.zpow_mem_zpowers tP k

theorem exists_star_three_unitarySixTwo {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hqp : q.p = 2) (hqe : q.exponent = 1) {S : Type}
    [Group S] [Finite S] (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) (hD81 : 81 ≤ Nat.card D) :
    ∃ E : Subgroup (MulAut S), E ≤ D ∧ Nat.card D ≤ 3 * Nat.card E ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨⟨hℓ, hf, -, -⟩, L, _, _, hL, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv eS
  have h : UnitaryFieldData q.p q.exponent L := ⟨hℓ, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 5 + 1) (K := L))
  let e : S ≃* primeFormP h ((1 : GL (Fin (5 + 1)) L) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) L) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  set cg := MulAut.congr e with hcg
  have hcD : Nat.card (D.map cg.toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective cg.injective
  obtain ⟨E', hE'D, hcard, U', hU'0, hU'2, hU'⟩ :=
    exists_star_three_u62 h hqp hqe rfl (D.map cg.toMonoidHom) (hD.map _) (by rw [hcD]; exact hD81)
  have hEA : E'.map cg.symm.toMonoidHom ≤ D := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨ψ, hψ, rfl⟩ := hE'D hφ'
    simpa using hψ
  have h3 : Nat.card (E'.map cg.symm.toMonoidHom) = Nat.card E' :=
    Subgroup.card_map_of_injective cg.symm.injective
  refine ⟨E'.map cg.symm.toMonoidHom, hEA, ?_, U'.map e.symm.toMonoidHom, ?_, hU'2.map _, ?_⟩
  · rw [h3, ← hcD]
    exact hcard
  · intro hb
    exact hU'0 ((Subgroup.map_eq_bot_iff_of_injective U' (f := e.symm.toMonoidHom) e.symm.injective).1 hb)
  · rintro _ ⟨φ', hφ', rfl⟩ _ ⟨u', hu', rfl⟩
    refine ⟨φ' u', hU' φ' hφ' u' hu', ?_⟩
    simp [hcg, MulAut.congr_apply]

end StarSix

section USixTwo

@[expose] def IsUSixTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA 5 q

theorem le_glbCore_of_unitarySixTwo {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : CFSG.Open.pRank 3 B = 4) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : IsUSixTwoIndex d)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  have hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope (.twistedA 5 q) :=
    ⟨hqp, by norm_num⟩
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hAel : IsElemAbelian 3 (CFSG.HardMathSupport.Dickson.I271.autImage B K) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isElemAbelian_autImage hB
  have hstab := InputsSeitz7.card_stab_eq (B := B) (K := K) hperf
  rw [hC, Subgroup.card_bot, mul_one, inf_eq_left.2 hBN, GL83.PiGen.card_eq_pow_pRank hB, hB4] at hstab
  obtain ⟨E, hEA, hEc, U, hU0, hU2, hUinv⟩ :=
    exists_star_three_unitarySixTwo hv hqp hqe e _ hAel (by rw [← hstab]; norm_num)
  have hEel : IsElemAbelian 3 E :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271_isElemAbelian_of_le hAel hEA
  obtain ⟨m₀, hm₀⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i271_exists_card_eq hp hEel
  have hm3 : 3 ≤ m₀ := by
    rw [← hstab, hm₀, ← pow_succ'] at hEc
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hEc
    omega
  have hc0 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 0 := by
    rw [hC]
    exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.pRank_bot_eq_zero' hp
  exact (InputsSeitz7.le_gammaPrime_of_seitz_rank
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.seitz2313Even_holds (k := 2) hperf hB
    (InputsSeitz7.odd_card_center_of_core hcore hK) hs e hEA hEel hm₀ (by omega) (by rw [hc0]; omega)
    ⟨U, hU0, hU2, hUinv⟩).trans (InputsSeitz7.gammaPrimeIn_le_glbCore le_rfl B K)

end USixTwo

section USixEight

open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom torusWit torusWit_apply torusWit_mem_SU
  sumZeroHom sum_sumZeroVec eq_one_of_torusWit_scalar unitary_of_mem_statedSU det_eq_one_of_linUni
  multiplicative_zmod_pow_eq_one card_multiplicative_zmod)

theorem five_le_pRank_of_psuSixEight {L : Type} [Field L] [Finite L] (hL : Nat.card L = (2 ^ 3) ^ 2)
    {G : Type} [Group G] [Finite G] (jG : StatedProj (StatedSU 6 (2 ^ 3) L) →* G)
    (hjG : Function.Injective jG) : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 L :=
    ⟨Nat.prime_two, by norm_num, by rw [hL]; norm_num⟩
  haveI : CharP L 2 := hU.charP
  haveI : Finite Lˣ := Finite.of_injective (fun u : Lˣ => (u : L)) (fun a b h => Units.ext h)
  let H := StatedSU 6 (2 ^ 3) L
  let C : Subgroup ↥H := (StatedScalars (Fin 6) L).subgroupOf H
  have hsinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 6) : Lˣ →* GL (Fin 6) L) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.scalar_injective (by norm_num)
  have hLu : Nat.card Lˣ = 63 := by rw [Nat.card_units, hL]; norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hgo : orderOf g = 63 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hLu]
  set η : Lˣ := g ^ 7 with hη
  have hηo : orderOf η = 9 := by
    rw [hη, orderOf_pow' g (by norm_num), hgo]
    norm_num
  have hη9 : η ^ 9 = 1 := by rw [← hηo]; exact pow_orderOf_eq_one η
  have hη3 : η ^ 3 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hηo] at this
    norm_num at this
  set ζ : Lˣ := η ^ 3 with hζ
  have hζ3 : ζ ^ 3 = 1 := by rw [hζ, ← pow_mul]; exact hη9
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hη3
  have hζu : ζ ^ (2 ^ 3 + 1) = 1 := by
    rw [show 2 ^ 3 + 1 = 3 * 3 by norm_num, pow_mul, hζ3, one_pow]
  let tw : Multiplicative (Fin 4 → ZMod 3) →* GL (Fin 6) L := torusWit ζ hζ3 (sumZeroHom 4)
  have htwH : ∀ u, tw u ∈ H := fun u =>
    torusWit_mem_SU (by norm_num) hζ3 hζu (sumZeroHom 4) sum_sumZeroVec u
  let φ : Multiplicative (Fin 4 → ZMod 3) →* ↥H ⧸ C := (QuotientGroup.mk' C).comp (tw.codRestrict H htwH)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hu
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hu
    refine Subgroup.mem_bot.2 (eq_one_of_torusWit_scalar hζ3 hζo (sumZeroHom 4)
      (Fin.castSucc (Fin.last 4)) (fun u => ?_) (fun u hu0 => ?_) u hc.symm)
    · show CFSG.SectionRank.OddCover.sumZeroVec u (Fin.castSucc (Fin.last 4)) = 0
      rw [CFSG.SectionRank.OddCover.sumZeroVec, Fin.snoc_castSucc, Fin.snoc_last]
    · funext i
      have := hu0 (Fin.castSucc (Fin.castSucc i))
      simpa [sumZeroHom, CFSG.SectionRank.OddCover.sumZeroVec] using this
  set sv : Fin 6 → Lˣ := Fin.snoc (fun _ : Fin 5 => η) (η ^ 4) with hsv
  have hsv9 : ∀ i, sv i ^ 9 = 1 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hsv, Fin.snoc_last, ← pow_mul, mul_comm, pow_mul, hη9, one_pow]
    · rw [hsv, Fin.snoc_castSucc, hη9]
  have hsv3 : ∀ i, sv i ^ 3 = η ^ 3 := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hsv, Fin.snoc_last, ← pow_mul, show 4 * 3 = 9 + 3 by norm_num, pow_add, hη9, one_mul]
    · rw [hsv, Fin.snoc_castSucc]
  have hsH : diagHom 6 sv ∈ H := by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [det_diagHom, Fin.prod_univ_castSucc]
      simp only [hsv, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_add, hη9, Units.val_one]
    · rw [coe_diagHom, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← pow_succ, ← Units.val_pow_eq_pow_val, show 2 ^ 3 + 1 = 9 by norm_num, hsv9 i,
        Units.val_one]
  set x : ↥H ⧸ C := QuotientGroup.mk (⟨diagHom 6 sv, hsH⟩ : ↥H) with hxdef
  have hs3 : (diagHom 6 sv) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) (η ^ 3) := by
    rw [← map_pow]
    apply Units.ext
    rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    congr 1
    funext i
    rw [Pi.pow_apply, hsv3 i]
  have hx : x ^ 3 = 1 := by
    rw [hxdef, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 ⟨η ^ 3, by rw [Subgroup.coe_pow]; exact hs3.symm⟩
  have hcommH : ∀ u, tw u * diagHom 6 sv = diagHom 6 sv * tw u := by
    intro u
    show torusWit ζ hζ3 (sumZeroHom 4) u * diagHom 6 sv = diagHom 6 sv * torusWit ζ hζ3 (sumZeroHom 4) u
    rw [torusWit_apply, ← map_mul, ← map_mul, mul_comm]
  have hcx : ∀ u, Commute (jG.comp φ u) (jG x) := by
    intro u
    have h1 : Commute (tw.codRestrict H htwH u) (⟨diagHom 6 sv, hsH⟩ : ↥H) := Subtype.ext (hcommH u)
    exact (h1.map (QuotientGroup.mk' C)).map jG
  have hxf : jG x ∉ (jG.comp φ).range := by
    rintro ⟨u, hu⟩
    have hu' : φ u = x := hjG hu
    have h1 := QuotientGroup.eq.1 hu'
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h1
    have hc' : Matrix.GeneralLinearGroup.scalar (Fin 6) c = (tw u)⁻¹ * diagHom 6 sv := hc
    have hcH : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ H := by
      rw [hc']
      exact mul_mem (inv_mem (htwH u)) hsH
    have hc6 : c ^ 6 = 1 := by
      have h := det_eq_one_of_linUni (p := 2) (f := 3) (Or.inr ⟨hL, rfl⟩) hcH
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have hc9 : c ^ 9 = 1 := by
      have h := unitary_of_mem_statedSU (p := 2) (f := 3) hL hcH
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map (by simp),
        Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at h
      have h0 := congrFun (Matrix.diagonal_injective h) 0
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, show 9 = 2 ^ 3 + 1 by norm_num, pow_succ, h0,
        Units.val_one])
    have hc3 : c ^ 3 = 1 := by
      calc c ^ 3 = c ^ 9 * (c ^ 6)⁻¹ := by group
        _ = 1 := by rw [hc9, hc6, inv_one, mul_one]
    have ht3 : (tw u) ^ 3 = 1 := by rw [← map_pow, multiplicative_zmod_pow_eq_one, map_one]
    have hst : diagHom 6 sv = tw u * Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      rw [hc', mul_inv_cancel_left]
    have hs31 : (diagHom 6 sv) ^ 3 = 1 := by
      rw [hst, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c (tw u)).mul_pow, ht3, one_mul,
        ← map_pow, hc3, map_one]
    rw [hs3] at hs31
    exact hη3 (hsinj (hs31.trans (map_one _).symm))
  have h := CFSG.HardMathSupport.Timmesfeld.LinearRank.le_pRank_of_extend Nat.prime_three
    (fun a b => mul_comm a b) multiplicative_zmod_pow_eq_one (card_multiplicative_zmod 4) (jG.comp φ)
    (hjG.comp hφ) (jG x) (by rw [← map_pow, hx, map_one]) hcx hxf
  omega

@[expose] def IsUSixEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .twistedA 5 q

theorem false_of_unitarySixEight {X : Type} [Group X] [Finite X] (hcore : GLAPPrimeCore 3 X = ⊥)
    {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : CFSG.Open.pRank 3 B = 4)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : IsUSixEightIndex d)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    False := by
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨-, L, _, _, hL, ⟨eT⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv eK
  rw [hqp, hqe] at eT hL
  have h5 := five_le_pRank_of_psuSixEight hL (K.subtype.comp eT.symm.toMonoidHom)
    (K.subtype_injective.comp eT.symm.injective)
  omega

end USixEight

section Residual

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsL2EightIndex Gen2318Index IsSixIndex)

@[expose] def Input23_19ExcThreeRest2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B →
      CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      B ≤ Subgroup.normalizer (K : Set X) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex 3 d.1 → d.1 ≠ .tits → ¬ IsL2EightIndex d.1 → ¬ Gen2318Index d.1 →
        ¬ InputsSeitz7.IsSpTwoIndex d → ¬ InputsSeitz7.IsUnitaryTwoIndex d →
        ¬ InputsSeitz7.IsSpEightIndex d → ¬ InputsSeitz7.IsUnitaryEightIndex d →
        ¬ InputsSeitz7.IsUThreeEightIndex d →
        ¬ IsOrthTwoIndex d → ¬ IsTriD4TwoIndex d → ¬ IsG2EightIndex d → ¬ InputsSeitz7.IsUSixIndex d →
        ¬ IsOmegaEightTwoIndex d → ¬ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsD4FourIndex d.1 →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        ((Subgroup.center ↥K ≠ ⊥ ∧ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 ∧
            B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) ∨
          B ⊓ Subgroup.centralizer (K : Set X) = ⊥) →
        K ≤ GLBCore 3 2 B

theorem not_coverIndex_d4_orthF2 {d : TauCeti.ValidLieTypeIndex}
    (hd : IsOmegaEightTwoIndex d ∨ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsD4FourIndex d.1) :
    ¬ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 := by
  rcases hd with ⟨q, -, -, hdq⟩ | hd
  · rw [hdq]
    exact id
  · obtain ⟨d0, hv⟩ := d
    cases d0 <;> first | exact hd.elim | exact id

theorem input23_19ExcThreeRest_of_rest2 (h : Input23_19ExcThreeRest2) :
    InputsSeitz7.Input23_19ExcThreeRest := by
  intro X _ _ hKX hcore B hB hB4 hrk K hK haut hsmall hBN d hd hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38 hU6
    hsix hrest
  obtain ⟨e⟩ := hd
  by_cases hnew : IsOrthTwoIndex d ∨ IsTriD4TwoIndex d ∨ IsG2EightIndex d
  · have hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
      hrest.resolve_left fun hc => not_coverIndex_orthF2 hnew hc.2.1
    rcases hnew with ho | ht
    · exact le_glbCore_of_orthTwoIndex hcore hB hB4 hrk hK d e ho hBN hC
    · exact (false_of_triD4Two_or_g2Eight hcore hB hB4 hrk hK d e ht hBN hC).elim
  by_cases hu6 : InputsSeitz7.IsUSixIndex d
  · obtain ⟨hC, h4⟩ := hU6 hu6
    obtain ⟨q, hqp, hqe | hqe, hdq⟩ := hu6
    · exact le_glbCore_of_unitarySixTwo hcore hB h4 hK d e ⟨q, hqp, hqe, hdq⟩ hBN hC
    · exact (false_of_unitarySixEight hcore hB h4 hrk hK d e ⟨q, hqp, hqe, hdq⟩ hBN hC).elim
  by_cases hD4 : IsOmegaEightTwoIndex d ∨ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsD4FourIndex d.1
  · have hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
      hrest.resolve_left fun hc => not_coverIndex_d4_orthF2 hD4 hc.2.1
    rcases hD4 with h8 | h44
    · exact le_glbCore_of_omegaEightTwo hcore hB hB4 hrk hK d e h8 hBN hC
    · exact (false_of_d4Four hcore hB hB4 hK d e h44 hBN hC (hsix (Or.inr (Or.inl h44)))).elim
  push Not at hnew hD4
  exact h X hKX hcore B hB hB4 hrk K hK haut hsmall hBN d ⟨e⟩ hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hnew.1 hnew.2.1 hnew.2.2 hu6 hD4.1 hD4.2 hsix hrest

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz8

end
