module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorModule
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor

open Module Subgroup CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModel
open CFSG.LocalAnalysis.ComponentInitial.SteinbergBX.TensorModule
open scoped IsMulCommutative

theorem ofAdd_one_mul_ofAdd_one :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by
  decide

section Linear

variable {C : Type*} [Group C] [Fact (Nat.Prime 2)] [CFSG.IsElementaryAbelian 2 C]

@[expose] def linAut (α : MulAut C) : Additive C ≃ₗ[ZMod 2] Additive C :=
  { (MulEquiv.toAdditive α : Additive C ≃+ Additive C) with
    map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive α : Additive C ≃+ Additive C) c x }

@[expose] def conjRep {H : Type*} [Group H] (κ : H →* MulAut C) :
    Representation (ZMod 2) H (Additive C) where
  toFun h := (linAut (κ h)).toLinearMap
  map_one' := LinearMap.ext fun x => by
    change linAut (κ 1) x = x
    rw [map_one]
    rfl
  map_mul' h h' := LinearMap.ext fun x => by
    change linAut (κ (h * h')) x = linAut (κ h) (linAut (κ h') x)
    rw [map_mul]
    rfl

theorem conjRep_ofMul {H : Type*} [Group H] (κ : H →* MulAut C) (h : H) (c : C) :
    conjRep κ h (Additive.ofMul c) = Additive.ofMul (κ h c) := rfl

theorem finrank_additive [Finite C] {n : ℕ} (hC : Nat.card C = 2 ^ n) :
    finrank (ZMod 2) (Additive C) = n := by
  have hp := FiniteField.pow_finrank_eq_natCard 2 (Additive C)
  rw [show Nat.card (Additive C) = Nat.card C from rfl, hC] at hp
  exact Nat.pow_right_injective le_rfl hp

end Linear

section Model

variable {F : Type*} [Group F] {C : Type*} [Group C] [Finite C]
  [Fact (Nat.Prime 2)] [CFSG.IsElementaryAbelian 2 C]

@[expose] def subOf (A : Subgroup C) : Submodule (ZMod 2) (Additive C) where
  carrier := {w | Additive.toMul w ∈ A}
  add_mem' {x y} hx hy := A.mul_mem hx hy
  zero_mem' := A.one_mem
  smul_mem' c w hw := by
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      exact A.one_mem
    · rw [one_smul]
      exact hw

omit [Finite C] in
theorem mem_subOf {A : Subgroup C} {w : Additive C} : w ∈ subOf A ↔ Additive.toMul w ∈ A :=
  Iff.rfl

theorem exists_model_of_two_factor (hC : Nat.card C = 2 ^ 12) (κ : F →* MulAut C)
    {Y : Type*} [Group Y] (θ : F →* Y) {R : Subgroup F} (hθker : θ.ker = R)
    {D : Subgroup Y} [D.Normal] (Ψ : D ≃* K) {a : F} (ha : a * a = 1)
    (hΨa : ∀ (d : Y) (hd : d ∈ D) (hda : (θ a)⁻¹ * d * θ a ∈ D), Ψ ⟨_, hda⟩ = (Ψ ⟨d, hd⟩).swap)
    (χ : Y →* Multiplicative (ZMod 2)) (hχa : χ (θ a) = Multiplicative.ofAdd 1) (hχ : χ.ker = D)
    {Q : Subgroup F} [Q.Normal] (hQD : Q.map θ = D) (hcomap : D.comap θ = R ⊔ Q)
    (hRQ : ∀ x ∈ D.comap θ, ∀ r ∈ R, x * r = r * x)
    (η : Q ≃* K) (hη : ∀ (q : Q) (hq : θ q ∈ D), η q = Ψ ⟨θ q, hq⟩)
    {A : Subgroup C} (hA : ∀ c : C, κ a c = c ↔ c ∈ A) (τ : Multiplicative Sym3 ≃* A)
    (hτ : ∀ (g : S) (B : Sym3), κ ((η.symm (g, g) : Q) : F) ((τ (Multiplicative.ofAdd B) : A) : C) =
      ((τ (Multiplicative.ofAdd (symThreeCongr g B)) : A) : C)) :
    ∃ (Ω : Y ≃* Ehat) (Φ : (Sym3 × Sym3) ≃ₗ[ZMod 2] Additive C),
      (∀ d : D, Ω d = SemidirectProduct.inl (Ψ d)) ∧ Ω (θ a) = sE ∧
      ∀ (f : F) (x : Sym3 × Sym3), conjRep κ f (Φ x) = Φ (rep12 (Ω (θ f)) x) := by
  classical
  have hā2 : θ a * θ a = 1 := by rw [← map_mul, ha, map_one]
  have hāinv : (θ a)⁻¹ = θ a := inv_eq_of_mul_eq_one_right hā2
  obtain ⟨Ω, hΩD, hΩa⟩ := exists_mulEquiv_Ehat D Ψ hā2 (fun d => by
    have hda : (θ a)⁻¹ * (d : Y) * θ a ∈ D := by
      have := (inferInstance : D.Normal).conj_mem _ d.2 (θ a)⁻¹
      rwa [inv_inv] at this
    have h2 : MulAut.conjNormal (θ a) d = ⟨_, hda⟩ := Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      change θ a * (d : Y) * (θ a)⁻¹ = (θ a)⁻¹ * d * θ a
      rw [hāinv])
    rw [h2, hΨa]) χ hχa hχ
  refine ⟨Ω, ?_⟩
  set ρF := conjRep κ with hρF
  set ρ : Representation (ZMod 2) K (Additive C) :=
    ρF.comp (Q.subtype.comp η.symm.toMonoidHom) with hρ
  set σ : Additive C →ₗ[ZMod 2] Additive C := ρF a with hσ
  have hρapply : ∀ k w, ρ k w = ρF ((η.symm k : Q) : F) w := fun k w => rfl
  have hθQ : ∀ q : Q, θ q ∈ D := fun q => hQD ▸ mem_map_of_mem θ q.2
  have hσσ : ∀ w, σ (σ w) = w := fun w => by
    change ρF a (ρF a w) = w
    rw [← Module.End.mul_apply, ← map_mul, ha, map_one, Module.End.one_apply]
  have hconj : ∀ k : K, a * ((η.symm k : Q) : F) * a⁻¹ = ((η.symm k.swap : Q) : F) := by
    intro k
    set q := η.symm k with hq
    have hmem : a * (q : F) * a⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem _ q.2 a
    have h1 : η ⟨_, hmem⟩ = k.swap := by
      have hθ' : θ (a * (q : F) * a⁻¹) = (θ a)⁻¹ * θ q * θ a := by
        rw [map_mul, map_mul, map_inv, hāinv]
      rw [hη ⟨_, hmem⟩ (hθQ _)]
      have e : (⟨θ (a * (q : F) * a⁻¹), hθQ ⟨_, hmem⟩⟩ : D) =
          ⟨(θ a)⁻¹ * θ q * θ a, hθ' ▸ hθQ ⟨_, hmem⟩⟩ := Subtype.ext hθ'
      rw [e, hΨa _ (hθQ q), ← hη q (hθQ q), hq, MulEquiv.apply_symm_apply]
    have h2 : (⟨_, hmem⟩ : Q) = η.symm k.swap := by rw [← h1, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h2
  have hσρ : ∀ k w, σ (ρ k w) = ρ k.swap (σ w) := fun k w => by
    change ρF a (ρF ((η.symm k : Q) : F) w) = ρF ((η.symm k.swap : Q) : F) (ρF a w)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← hconj k]
    congr 2
    group
  set Asub := subOf A with hAsub
  have hAiff : ∀ w, w ∈ Asub ↔ σ w = w := fun w => by
    rw [mem_subOf, ← hA]
    constructor
    · intro h
      exact congrArg Additive.ofMul h
    · intro h
      exact congrArg Additive.toMul h
  let β₀ : Sym3 →+ Additive C :=
    { toFun := fun B => Additive.ofMul ((τ (Multiplicative.ofAdd B) : A) : C)
      map_zero' := by simp
      map_add' := fun B B' => by
        rw [ofAdd_add, map_mul, Subgroup.coe_mul]
        rfl }
  have hβ₀mem : ∀ B, β₀ B ∈ Asub := fun B => (τ (Multiplicative.ofAdd B)).2
  let β₁ : Sym3 →ₗ[ZMod 2] Asub :=
    (AddMonoidHom.toZModLinearMap 2 β₀).codRestrict Asub hβ₀mem
  have hβ₁bij : Function.Bijective β₁ := by
    constructor
    · intro B B' h
      have h1 : ((τ (Multiplicative.ofAdd B) : A) : C) = ((τ (Multiplicative.ofAdd B') : A) : C) :=
        congrArg (fun x : Asub => Additive.toMul (x : Additive C)) h
      exact Multiplicative.ofAdd.injective (τ.injective (Subtype.ext h1))
    · rintro ⟨w, hw⟩
      refine ⟨Multiplicative.toAdd (τ.symm ⟨Additive.toMul w, hw⟩), Subtype.ext ?_⟩
      change Additive.ofMul ((τ (Multiplicative.ofAdd (Multiplicative.toAdd
        (τ.symm ⟨Additive.toMul w, hw⟩))) : A) : C) = w
      rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rfl
  let β : Sym3 ≃ₗ[ZMod 2] Asub := LinearEquiv.ofBijective β₁ hβ₁bij
  have hβapply : ∀ B, (β B : Additive C) = Additive.ofMul ((τ (Multiplicative.ofAdd B) : A) : C) :=
    fun B => rfl
  have hβ : ∀ (g : S) (B : Sym3), ρ (g, g) (β B : Additive C) = β (symThreeCongr g B) :=
    fun g B => by
      rw [hρapply, hβapply, hβapply, hρF, conjRep_ofMul, hτ]
  have hW : finrank (ZMod 2) (Additive C) = 12 := finrank_additive hC
  have hdA : finrank (ZMod 2) Asub = 6 := by rw [← β.finrank_eq, finrank_sym3]
  have hAr : ∀ x ∈ Asub, ∃ w, σ w + w = x := by
    set f : Additive C →ₗ[ZMod 2] Additive C := σ + LinearMap.id with hf
    have hrange : LinearMap.range f ≤ Asub := by
      rintro _ ⟨w, rfl⟩
      rw [hAiff]
      simp only [hf, LinearMap.add_apply, LinearMap.id_apply, map_add, hσσ, add_comm]
    have hker : LinearMap.ker f = Asub := by
      ext w
      rw [LinearMap.mem_ker, hAiff]
      simp only [hf, LinearMap.add_apply, LinearMap.id_apply]
      constructor
      · intro h
        have := congrArg (· + w) h
        simpa [add_assoc, ZModModule.add_self] using this
      · intro h
        rw [h, ZModModule.add_self]
    have hsum := LinearMap.finrank_range_add_finrank_ker f
    rw [hker, hdA, hW] at hsum
    have heq : LinearMap.range f = Asub :=
      Submodule.eq_of_le_of_finrank_eq hrange (by rw [hdA]; omega)
    intro x hx
    rw [← heq] at hx
    obtain ⟨w, rfl⟩ := hx
    exact ⟨w, rfl⟩
  obtain ⟨Φ, hΦρ, hΦσ⟩ := exists_model_equiv ρ σ hσσ hσρ Asub hAiff β hβ hAr hW
  refine ⟨Φ, hΩD, hΩa, ?_⟩
  have hQcomap : ∀ q : Q, (q : F) ∈ D.comap θ := fun q => hθQ q
  have hRtriv : ∀ r ∈ R, ∀ w, ρF r w = w := by
    intro r hr
    let τr : (Sym3 × Sym3) ≃ₗ[ZMod 2] (Sym3 × Sym3) := (Φ.trans (linAut (κ r))).trans Φ.symm
    have hτr : ∀ x, τr x = Φ.symm (ρF r (Φ x)) := fun x => rfl
    have hcomm : ∀ (k : K) (x : Sym3 × Sym3), τr (repK12 k x) = repK12 k (τr x) := by
      intro k x
      rw [hτr, hτr, ← hΦρ, Φ.symm_apply_eq, ← hΦρ, Φ.apply_symm_apply, hρapply, hρapply,
        ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        hRQ _ (hQcomap (η.symm k)) r hr]
    intro w
    obtain ⟨x, rfl⟩ := Φ.surjective w
    have h1 := eq_refl_of_commute12 τr hcomm x
    rw [hτr, Φ.symm_apply_eq] at h1
    exact h1
  have hΩQ : ∀ q : Q, Ω (θ q) = SemidirectProduct.inl (η q) := fun q => by
    rw [hη q (hθQ q)]
    exact hΩD ⟨θ q, hθQ q⟩
  have hΩR : ∀ r ∈ R, Ω (θ r) = 1 := fun r hr => by
    rw [show θ r = 1 from (hθker ▸ hr : r ∈ θ.ker), map_one]
  have hRQmul : ∀ x ∈ D.comap θ, ∃ r ∈ R, ∃ q : Q, x = r * q := by
    intro x hx
    have hRn : R.Normal := hθker ▸ MonoidHom.normal_ker θ
    rw [hcomap, ← SetLike.mem_coe, Subgroup.normal_mul] at hx
    obtain ⟨r, hr, q, hq, rfl⟩ := hx
    exact ⟨r, hr, ⟨q, hq⟩, rfl⟩
  have hinner : ∀ (r : F) (hr : r ∈ R) (q : Q) (x : Sym3 × Sym3),
      ρF (r * q) (Φ x) = Φ (rep12 (Ω (θ (r * q))) x) := by
    intro r hr q x
    rw [map_mul, map_mul, Module.End.mul_apply, map_mul, hΩR r hr, one_mul, hΩQ, rep12_inl,
      hRtriv r hr, show (q : F) = ((η.symm (η q) : Q) : F) by rw [MulEquiv.symm_apply_apply],
      ← hρapply, hΦρ]
  intro f x
  rcases mult_two_cases (χ (θ f)) with h | h
  · have hf : f ∈ D.comap θ := by
      rw [mem_comap, ← hχ]
      exact h
    obtain ⟨r, hr, q, rfl⟩ := hRQmul f hf
    exact hinner r hr q x
  · have hf : f * a ∈ D.comap θ := by
      rw [mem_comap, ← hχ, MonoidHom.mem_ker, map_mul, map_mul, h, hχa]
      exact ofAdd_one_mul_ofAdd_one
    obtain ⟨r, hr, q, hrq⟩ := hRQmul (f * a) hf
    have hfeq : f = r * q * a := by
      rw [← hrq, mul_assoc, ha, mul_one]
    rw [hfeq, map_mul, Module.End.mul_apply, show θ (r * q * a) = θ (r * q) * θ a from
      map_mul θ _ _, map_mul Ω]
    change ρF (r * q) (σ (Φ x)) = Φ (rep12 (Ω (θ (r * q)) * Ω (θ a)) x)
    rw [hΦσ, hinner r hr q, hΩa, rep12_mul_apply, rep12_sE_apply]

end Model

end CFSG.LocalAnalysis.ComponentInitial.ChevTwoFactor
