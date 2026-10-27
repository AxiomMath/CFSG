module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4FixQS

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

section Quadratic

theorem ringEquiv_apply_apply_of_sq_eq_one {F : Type} [Field F] (σ : F ≃+* F) (hσ2 : σ ^ 2 = 1)
    (x : F) : σ (σ x) = x := by
  have := congrArg (fun f : F ≃+* F => f x) hσ2
  simpa [pow_two] using this

theorem exists_apply_ne_of_ne_one {F : Type} [Field F] (σ : F ≃+* F) (hσ1 : σ ≠ 1) :
    ∃ x : F, σ x ≠ x := by
  by_contra h
  push Not at h
  exact hσ1 (RingEquiv.ext fun x => h x)

theorem hilbert90_of_sq_eq_one {F : Type} [Field F] (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 = 1)
    {ν : F} (hν0 : ν ≠ 0) (hν : ν * σ ν = 1) : ∃ l : F, l ≠ 0 ∧ σ l = ν * l := by
  have hσσ := ringEquiv_apply_apply_of_sq_eq_one σ hσ2
  have hσν : σ ν = ν⁻¹ := eq_inv_of_mul_eq_one_right hν
  have key : ∀ c : F, σ (c + ν⁻¹ * σ c) = ν * (c + ν⁻¹ * σ c) := by
    intro c
    rw [map_add, map_mul, map_inv₀, hσσ, hσν, inv_inv]
    field_simp
    ring
  by_cases h1 : (1 : F) + ν⁻¹ * σ 1 = 0
  · obtain ⟨e, he⟩ := exists_apply_ne_of_ne_one σ hσ1
    have hν1 : ν⁻¹ = -1 := by
      rw [map_one, mul_one] at h1
      exact eq_neg_of_add_eq_zero_right h1
    refine ⟨e + ν⁻¹ * σ e, ?_, key e⟩
    rw [hν1]
    intro h
    apply he
    linear_combination -h
  · exact ⟨_, h1, key 1⟩

theorem exists_mul_apply_eq_of_apply_eq {F : Type} [Field F] [Finite F] (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : σ ^ 2 = 1) {d : F} (hd0 : d ≠ 0) (hd : σ d = d) : ∃ ρ : F, ρ ≠ 0 ∧ ρ * σ ρ = d := by
  have hσσ := ringEquiv_apply_apply_of_sq_eq_one σ hσ2
  let σu : Fˣ →* Fˣ := Units.map σ.toRingHom.toMonoidHom
  let ψ : Fˣ →* Fˣ := MonoidHom.mk' (fun x => x * σu x) (fun a b => by
    simp only [map_mul]
    exact mul_mul_mul_comm _ _ _ _)
  let φ : Fˣ →* Fˣ := MonoidHom.mk' (fun x => σu x * x⁻¹) (fun a b => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hψ : ∀ x : Fˣ, ((ψ x : Fˣ) : F) = (x : F) * σ (x : F) := fun x => rfl
  have hφ : ∀ x : Fˣ, ((φ x : Fˣ) : F) = σ (x : F) * (x : F)⁻¹ := fun x => by
    show ((σu x * x⁻¹ : Fˣ) : F) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hker : ∀ x : Fˣ, x ∈ φ.ker ↔ σ (x : F) = x := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg (fun u : Fˣ => (u : F)) h
      simp only [hφ, Units.val_one] at this
      field_simp at this
      exact this
    · intro h
      apply Units.ext
      rw [hφ, h, Units.val_one]
      exact mul_inv_cancel₀ x.ne_zero
  have hkerψ : ∀ x : Fˣ, x ∈ ψ.ker ↔ (x : F) * σ (x : F) = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg (fun u : Fˣ => (u : F)) h
      simpa [hψ] using this
    · intro h
      exact Units.ext (by rw [hψ, h, Units.val_one])
  have h1 : φ.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hkerψ, hφ]
    rw [map_mul, map_inv₀, hσσ]
    field_simp
  have h2 : ψ.ker ≤ φ.range := by
    intro x hx
    rw [hkerψ] at hx
    obtain ⟨l, hl0, hl⟩ := hilbert90_of_sq_eq_one σ hσ1 hσ2 x.ne_zero hx
    refine ⟨Units.mk0 l hl0, ?_⟩
    apply Units.ext
    rw [hφ]
    simp only [Units.val_mk0]
    rw [hl]
    field_simp
  have h3 : ψ.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hker, hψ, map_mul, hσσ]
    exact mul_comm _ _
  have hc1 := Subgroup.card_ker_mul_card_range φ
  have hc2 := Subgroup.card_ker_mul_card_range ψ
  have heq : φ.range = ψ.ker := le_antisymm h1 h2
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hcard : Nat.card φ.ker = Nat.card ψ.range := by
    rw [heq] at hc1
    have : Nat.card ψ.ker * Nat.card φ.ker = Nat.card ψ.ker * Nat.card ψ.range := by
      rw [mul_comm (Nat.card ψ.ker), hc1, hc2]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hrange : ψ.range = φ.ker :=
    Subgroup.eq_of_le_of_card_ge h3 hcard.le
  have hdmem : Units.mk0 d hd0 ∈ φ.ker := (hker _).mpr (by simpa using hd)
  rw [← hrange] at hdmem
  obtain ⟨x, hx⟩ := hdmem
  refine ⟨x, x.ne_zero, ?_⟩
  have := congrArg (fun u : Fˣ => (u : F)) hx
  simpa [hψ] using this

end Quadratic

section Transvection

variable {F : Type} [Field F]

theorem symplectic_of_ωJ_mulVec {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : ∀ x y, ωJ F (M *ᵥ x) (M *ᵥ y) = ωJ F x y) : Mᵀ * formJ 2 F * M = formJ 2 F := by
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  apply LinearMap.ext₂
  intro x y
  have := h x y
  simpa [ωJ] using this

theorem ωJ_mulVec_of_similitude {a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {μ : F}
    (ha : aᵀ * formJ 2 F * a = μ • formJ 2 F) (x y : Fin 2 ⊕ Fin 2 → F) :
    ωJ F (a *ᵥ x) (a *ᵥ y) = μ * ωJ F x y := by
  rw [ωJ_apply, ωJ_apply, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ha,
    ← Matrix.dotProduct_mulVec]
  simp [Matrix.smul_mulVec, dotProduct_smul]

theorem ωJ_map_ringEquiv (σ : F ≃+* F) (x y : Fin 2 ⊕ Fin 2 → F) :
    σ (ωJ F x y) = ωJ F (σ ∘ x) (σ ∘ y) := by
  have h1 : (σ ∘ (formJ 2 F *ᵥ y)) = formJ 2 F *ᵥ (σ ∘ y) := by
    ext i
    have hJ : (formJ 2 F).map σ.toRingHom = formJ 2 F := formJ_map σ
    have := RingHom.map_mulVec σ.toRingHom (formJ 2 F) y i
    rw [hJ] at this
    exact this
  have h2 := RingHom.map_dotProduct σ.toRingHom x (formJ 2 F *ᵥ y)
  rw [ωJ_apply, ωJ_apply]
  refine h2.trans ?_
  exact congrArg (fun w => (σ ∘ x) ⬝ᵥ w) h1

theorem mulVec_comp_smul_ringEquiv {ι : Type} [Fintype ι] (σ : F ≃+* F) (a : Matrix ι ι F) (c : F)
    (x : ι → F) : a *ᵥ (σ ∘ (c • x)) = σ c • (a *ᵥ (σ ∘ x)) := by
  have : σ ∘ (c • x) = σ c • (σ ∘ x) := by
    ext i
    simp
  rw [this, Matrix.mulVec_smul]

theorem mulVec_comp_add_ringEquiv {ι : Type} [Fintype ι] (σ : F ≃+* F) (a : Matrix ι ι F)
    (x y : ι → F) : a *ᵥ (σ ∘ (x + y)) = a *ᵥ (σ ∘ x) + a *ᵥ (σ ∘ y) := by
  have : σ ∘ (x + y) = σ ∘ x + σ ∘ y := by
    ext i
    simp
  rw [this, Matrix.mulVec_add]

@[expose] def symTransv (l : F) (v : Fin 2 ⊕ Fin 2 → F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  1 + l • Matrix.vecMulVec v (formJ 2 F *ᵥ v)

theorem symTransv_mulVec (l : F) (v x : Fin 2 ⊕ Fin 2 → F) :
    symTransv l v *ᵥ x = x + (l * ωJ F x v) • v := by
  rw [symTransv, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul, ωJ_apply, dotProduct_comm]

theorem symTransv_symplectic (l : F) (v : Fin 2 ⊕ Fin 2 → F) :
    (symTransv l v)ᵀ * formJ 2 F * symTransv l v = formJ 2 F := by
  apply symplectic_of_ωJ_mulVec
  intro x y
  rw [symTransv_mulVec, symTransv_mulVec]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, ωJ_self]
  rw [ωJ_comm v y]
  ring

@[expose] def symTransvSp (l : F) (v : Fin 2 ⊕ Fin 2 → F) : StatedSp 2 F :=
  toSp (symTransv l v) (symTransv_symplectic l v)

theorem coe_symTransvSp (l : F) (v : Fin 2 ⊕ Fin 2 → F) :
    (((symTransvSp l v : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = symTransv l v := rfl

theorem map_symTransv (σ : F ≃+* F) (l : F) (v : Fin 2 ⊕ Fin 2 → F) :
    (symTransv l v).map σ = symTransv (σ l) (σ ∘ v) := by
  have hJ : (formJ 2 F).map σ.toRingHom = formJ 2 F := formJ_map σ
  have hw : ∀ j, σ ((formJ 2 F *ᵥ v) j) = (formJ 2 F *ᵥ (σ ∘ v)) j := fun j => by
    have := RingHom.map_mulVec σ.toRingHom (formJ 2 F) v j
    rw [hJ] at this
    exact this
  ext i j
  simp only [symTransv, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_add, map_mul, hw, Matrix.one_apply, Function.comp_apply]
  by_cases h : i = j <;> simp [h]

theorem symTransvSp_mem_fixOf (A : gsp 2 F) (σ : F ≃+* F) {ρ l : F} (hρ : ρ ≠ 0)
    (hl : σ l * ρ ^ 2 = (multiplierUnit A : F) * l) {v : Fin 2 ⊕ Fin 2 → F}
    (hv : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ (σ ∘ v) =
      ρ • v) :
    symTransvSp l v ∈ fixOf (conjSp 2 F A * fieldSp 2 F σ) := by
  set a := ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with ha
  have hμ : aᵀ * formJ 2 F * a = (multiplierUnit A : F) • formJ 2 F := multiplierUnit_spec A
  have hvρ : v = ρ⁻¹ • (a *ᵥ (σ ∘ v)) := by
    rw [hv, smul_smul, inv_mul_cancel₀ hρ, one_smul]
  have hkey : ∀ y, a *ᵥ ((symTransv l v).map σ *ᵥ y) = symTransv l v *ᵥ (a *ᵥ y) := by
    intro y
    rw [map_symTransv, symTransv_mulVec, symTransv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      hv, smul_smul]
    congr 1
    have h1 : ωJ F (a *ᵥ y) v = ρ⁻¹ * ((multiplierUnit A : F) * ωJ F y (σ ∘ v)) := by
      conv_lhs => rw [hvρ]
      rw [map_smul, smul_eq_mul, ωJ_mulVec_of_similitude hμ]
    rw [h1]
    congr 1
    field_simp
    linear_combination (ωJ F y (σ ∘ v)) * hl
  have hkey' : a * (symTransv l v).map σ = symTransv l v * a := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro y
    simpa [Matrix.toLin'_mul, Matrix.toLin'_apply] using hkey y
  rw [mem_fixOf]
  apply sp_ext
  change ((A : GL (Fin 2 ⊕ Fin 2) F) * ((fieldSp 2 F σ (symTransvSp l v) : StatedSp 2 F) : GL _ F) *
      (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F).val = _
  rw [Units.val_mul, Units.val_mul, coe_fieldSp, coe_symTransvSp, hkey', Matrix.mul_assoc]
  have : a * ((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F).val = 1 := Units.mul_inv _
  rw [this, Matrix.mul_one]

end Transvection

theorem exists_eigen_data {F : Type} [Field F] [Finite F] (A : gsp 2 F) (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : σ ^ 2 = 1) (d : Fˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) F) * glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d) :
    ∃ (ρ l ε₀ : F) (vy : (Fin 2 ⊕ Fin 2 → F) → (Fin 2 ⊕ Fin 2 → F)), ρ ≠ 0 ∧ l ≠ 0 ∧
      σ ε₀ ≠ ε₀ ∧ σ l * ρ ^ 2 = (multiplierUnit A : F) * l ∧
      (∀ y, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        (σ ∘ vy y) = ρ • vy y) ∧
      (∀ y, (σ ε₀ - ε₀) • y = σ ε₀ • vy y - vy (ε₀ • y)) := by
  set a := ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with ha
  set μ : F := (multiplierUnit A : F) with hμdef
  have hμ : aᵀ * formJ 2 F * a = μ • formJ 2 F := multiplierUnit_spec A
  have hσσ := ringEquiv_apply_apply_of_sq_eq_one σ hσ2
  have hd' : a * a.map σ = (d : F) • 1 := by
    have h := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hd
    simp only [Units.val_mul] at h
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal] at h
    exact h
  have hτ_smul := mulVec_comp_smul_ringEquiv σ a
  have hτ_add := mulVec_comp_add_ringEquiv σ a
  have hσmul : ∀ x : Fin 2 ⊕ Fin 2 → F, σ ∘ (a *ᵥ x) = a.map σ *ᵥ (σ ∘ x) := by
    intro x
    ext i
    exact RingHom.map_mulVec σ.toRingHom a x i
  have hτ2 : ∀ x : Fin 2 ⊕ Fin 2 → F, a *ᵥ (σ ∘ (a *ᵥ (σ ∘ x))) = (d : F) • x := by
    intro x
    have e : σ ∘ (σ ∘ x) = x := by
      funext i
      exact hσσ (x i)
    rw [hσmul, e, Matrix.mulVec_mulVec, hd', Matrix.smul_mulVec, Matrix.one_mulVec]
  have hσd : σ (d : F) = d := by
    obtain ⟨x, hx⟩ : ∃ x : Fin 2 ⊕ Fin 2 → F, a *ᵥ (σ ∘ x) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have h1 := hτ2 (fun _ => (1 : F))
      rw [hcon (a *ᵥ (σ ∘ (fun _ => (1 : F))))] at h1
      have h2 := congrFun h1 (Sum.inl 0)
      exact d.ne_zero (by simpa using h2.symm)
    have e1 := hτ2 (a *ᵥ (σ ∘ x))
    have e2 : a *ᵥ (σ ∘ (a *ᵥ (σ ∘ (a *ᵥ (σ ∘ x))))) = σ (d : F) • (a *ᵥ (σ ∘ x)) := by
      rw [hτ2 x]
      exact hτ_smul d x
    rw [e1] at e2
    have : ((d : F) - σ (d : F)) • (a *ᵥ (σ ∘ x)) = 0 := by
      rw [sub_smul, e2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hx
  have hτform : ∀ x y : Fin 2 ⊕ Fin 2 → F,
      ωJ F (a *ᵥ (σ ∘ x)) (a *ᵥ (σ ∘ y)) = μ * σ (ωJ F x y) := by
    intro x y
    rw [ωJ_mulVec_of_similitude hμ, ωJ_map_ringEquiv]
  have hμd : μ * σ μ = (d : F) ^ 2 := by
    set x : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1 with hx
    set y : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inr 0) 1 with hy
    have h1 : ωJ F x y = 1 := pairedSympForm_single (k := F) (m := 2) 0
    have h2 := hτform (a *ᵥ (σ ∘ x)) (a *ᵥ (σ ∘ y))
    rw [hτ2 x, hτ2 y, hτform x y, h1, map_mul, hσσ] at h2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, h1] at h2
    linear_combination -h2
  obtain ⟨ρ, hρ0, hρ⟩ := exists_mul_apply_eq_of_apply_eq σ hσ1 hσ2 d.ne_zero hσd
  have hσρ0 : σ ρ ≠ 0 := by simpa using hρ0
  have hν0 : μ / ρ ^ 2 ≠ 0 := div_ne_zero (multiplierUnit A).ne_zero (pow_ne_zero 2 hρ0)
  have hν : (μ / ρ ^ 2) * σ (μ / ρ ^ 2) = 1 := by
    rw [map_div₀, map_pow]
    field_simp
    rw [hμd, ← hρ]
    ring
  obtain ⟨l, hl0, hl⟩ := hilbert90_of_sq_eq_one σ hσ1 hσ2 hν0 hν
  have hl' : σ l * ρ ^ 2 = μ * l := by
    rw [hl]
    field_simp
  obtain ⟨ε₀, hε⟩ := exists_apply_ne_of_ne_one σ hσ1
  have hσρinv : σ ρ⁻¹ * (d : F) = ρ := by
    rw [map_inv₀, ← hρ]
    field_simp
  refine ⟨ρ, l, ε₀, fun y => y + ρ⁻¹ • (a *ᵥ (σ ∘ y)), hρ0, hl0, hε, hl', ?_, ?_⟩
  · intro y
    have e1 : a *ᵥ (σ ∘ (y + ρ⁻¹ • (a *ᵥ (σ ∘ y)))) = a *ᵥ (σ ∘ y) + (σ ρ⁻¹ * d) • y := by
      rw [hτ_add, hτ_smul, hτ2, smul_smul]
    rw [e1, hσρinv, smul_add, smul_smul, mul_inv_cancel₀ hρ0, one_smul, add_comm]
  · intro y
    show (σ ε₀ - ε₀) • y = σ ε₀ • (y + ρ⁻¹ • (a *ᵥ (σ ∘ y))) -
      (ε₀ • y + ρ⁻¹ • (a *ᵥ (σ ∘ (ε₀ • y))))
    rw [hτ_smul]
    module

theorem field_no_invariant_isotropic {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (A : gsp 2 F) (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 = 1) (d : Fˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) F) * glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d)
    (W : Submodule F (Fin 2 ⊕ Fin 2 → F)) (hW0 : W ≠ ⊥)
    (hWiso : IsTotallyIsotropic (pairedSympForm F 2) W)
    (hinv : ∀ g ∈ fixOf (conjSp 2 F A * fieldSp 2 F σ), ∀ w ∈ W,
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w ∈ W) : False := by
  let _ := hodd
  obtain ⟨ρ, l, ε₀, vy, hρ, hl0, hε, hl, hvy, hspan⟩ := exists_eigen_data A σ hσ1 hσ2 d hd
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hB : ∀ v, ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
      (σ ∘ v) = ρ • v → ωJ F x v = 0 := by
    intro v hv
    by_contra hne
    have hT := hinv _ (symTransvSp_mem_fixOf A σ hρ hl hv) x hxW
    rw [coe_symTransvSp, symTransv_mulVec] at hT
    have h1 : (l * ωJ F x v) • v ∈ W := by
      have := W.sub_mem hT hxW
      simpa using this
    have h2 : v ∈ W := by
      have := W.smul_mem (l * ωJ F x v)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hl0 hne), one_smul] at this
    exact hne (hWiso x hxW v h2)
  apply hx0
  apply ωJ_nondeg
  intro y
  have h1 : (σ ε₀ - ε₀) * ωJ F x y = 0 := by
    have := congrArg (ωJ F x) (hspan y)
    simp only [map_smul, map_sub, smul_eq_mul, hB _ (hvy y), hB _ (hvy (ε₀ • y))] at this
    simpa using this
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hε)

theorem field_centralizer_scalar {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (A : gsp 2 F) (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 = 1) (d : Fˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) F) * glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d)
    (x : StatedSp 2 F) (hx : ∀ g ∈ fixOf (conjSp 2 F A * fieldSp 2 F σ), x * g = g * x) :
    x ∈ spScalars 2 F := by
  let _ := hodd
  obtain ⟨ρ, l, ε₀, vy, hρ, hl0, hε, hl, hvy, hspan⟩ := exists_eigen_data A σ hσ1 hσ2 d hd
  set a := ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with ha
  set X := ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hX
  have hline : ∀ v, a *ᵥ (σ ∘ v) = ρ • v → v ≠ 0 → ∃ c : F, X *ᵥ v = c • v := by
    intro v hv hv0
    have hcomm := hx _ (symTransvSp_mem_fixOf A σ hρ hl hv)
    have hXT : X * symTransv l v = symTransv l v * X := by
      have := congrArg (fun g : StatedSp 2 F =>
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hcomm
      simpa [coe_symTransvSp] using this
    obtain ⟨y, hy⟩ : ∃ y, ωJ F y v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (ωJ_nondeg fun y => by rw [ωJ_comm, hcon y, neg_zero])
    have h1 : X *ᵥ (symTransv l v *ᵥ y) = symTransv l v *ᵥ (X *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hXT]
    rw [symTransv_mulVec, symTransv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    have h2 : (l * ωJ F y v) • (X *ᵥ v) = (l * ωJ F (X *ᵥ y) v) • v := add_left_cancel h1
    refine ⟨(l * ωJ F y v)⁻¹ * (l * ωJ F (X *ᵥ y) v), ?_⟩
    rw [← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ (mul_ne_zero hl0 hy), one_smul]
  obtain ⟨y₀, hy₀⟩ : ∃ y, vy y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := hspan (fun _ => 1)
    rw [hcon, hcon, smul_zero, sub_zero] at h
    have h' := congrFun h (Sum.inl 0)
    simp only [Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at h'
    exact hε (sub_eq_zero.mp h')
  obtain ⟨c₀, hc₀⟩ := hline (vy y₀) (hvy y₀) hy₀
  have hall : ∀ v, a *ᵥ (σ ∘ v) = ρ • v → X *ᵥ v = c₀ • v := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp
    obtain ⟨c, hc⟩ := hline v hv hv0
    by_cases hdep : ∃ t : F, v = t • vy y₀
    · obtain ⟨t, rfl⟩ := hdep
      rw [Matrix.mulVec_smul, hc₀, smul_comm]
    · push Not at hdep
      have hsum : a *ᵥ (σ ∘ (v + vy y₀)) = ρ • (v + vy y₀) := by
        rw [mulVec_comp_add_ringEquiv, hv, hvy y₀, smul_add]
      have hsum0 : v + vy y₀ ≠ 0 := by
        intro h0
        apply hdep (-1)
        rw [neg_one_smul]
        exact eq_neg_of_add_eq_zero_left h0
      obtain ⟨c', hc'⟩ := hline _ hsum hsum0
      rw [Matrix.mulVec_add, hc, hc₀] at hc'
      have h3 : (c' - c) • v + (c' - c₀) • vy y₀ = 0 := by
        have : c' • (v + vy y₀) - (c • v + c₀ • vy y₀) = 0 := by rw [← hc', sub_self]
        rw [← this]
        module
      have h4 : c' - c = 0 := by
        by_contra h
        apply hdep (-((c' - c)⁻¹ * (c' - c₀)))
        have h5 : (c' - c) • v = -((c' - c₀) • vy y₀) := eq_neg_of_add_eq_zero_left
          (by simpa using h3)
        calc v = (c' - c)⁻¹ • ((c' - c) • v) := by rw [smul_smul, inv_mul_cancel₀ h, one_smul]
          _ = -((c' - c)⁻¹ * (c' - c₀)) • vy y₀ := by rw [h5, smul_neg, smul_smul, neg_smul]
      have h5 : c' - c₀ = 0 := by
        rw [h4, zero_smul, zero_add] at h3
        exact (smul_eq_zero.mp h3).resolve_right hy₀
      rw [hc, show c = c₀ by linear_combination h5 - h4]
  have hXy : ∀ y, X *ᵥ y = c₀ • y := by
    intro y
    have h1 := congrArg (fun z => X *ᵥ z) (hspan y)
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, hall _ (hvy y),
      hall _ (hvy (ε₀ • y))] at h1
    have h2 : (σ ε₀ - ε₀) • (X *ᵥ y) = (σ ε₀ - ε₀) • (c₀ • y) := by
      rw [h1, smul_comm (σ ε₀ - ε₀) c₀ y, hspan y, smul_sub, smul_comm c₀ (σ ε₀)]
    exact smul_right_injective _ (sub_ne_zero.mpr hε) h2
  have hXmat : X = c₀ • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro y
    simp [Matrix.toLin'_apply, hXy y]
  have hsq : c₀ * c₀ = 1 := by
    have h := symplectic_of_mem x
    rw [← hX, hXmat] at h
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul] at h
    have := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
    simpa [formJ] using this
  rw [mem_spScalars_iff]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    rw [← hX, hXmat, h, one_smul]
  · right
    rw [← hX, hXmat, h, neg_smul, one_smul]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
