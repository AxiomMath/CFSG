module

public import CFSG.CGT.Foote82.T66.CitedMC2
import CFSG.CGT.Foote82.T66.CertProofsL13Alt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 Equiv Equiv.Perm

namespace A11Aux

@[expose] def s1 : Perm (Fin 11) := swap 0 1 * swap 1 2 * swap 3 4 * swap 4 5

@[expose] def s2 : Perm (Fin 11) := swap 5 6 * swap 6 7 * swap 8 9 * swap 9 10

@[expose] def s3 : Perm (Fin 11) := swap 0 1 * swap 1 3 * swap 2 4 * swap 4 8

@[expose] def g2 : Perm (Fin 11) := finRotate 11 ^ 5

@[expose] def g3 : Perm (Fin 11) := swap 2 3 * swap 5 8 * swap 8 7 * swap 7 6

theorem perm_facts : g2 * s1 * g2⁻¹ = s2 ∧ g3 * s1 * g3⁻¹ = s3 ∧ (s1 * s2 * s3) ^ 11 = 1 ∧
    s1 * s2 * s3 ≠ 1 := by
  decide +kernel

theorem sign_g2 : sign g2 = 1 := by
  rw [g2, map_pow, sign_finRotate]
  decide

theorem sign_g3 : sign g3 = 1 := by
  rw [g3, map_mul, map_mul, map_mul, sign_swap (by decide), sign_swap (by decide),
    sign_swap (by decide), sign_swap (by decide)]
  decide

theorem cycleType_s1 : s1.cycleType = {3, 3} := by
  have e : s1 = (swap 0 2 * swap 0 1) * (swap 3 5 * swap 3 4) := by decide +kernel
  have h1 : IsThreeCycle (swap (0 : Fin 11) 2 * swap 0 1) :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have h2 : IsThreeCycle (swap (3 : Fin 11) 5 * swap 3 4) :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have hd : Perm.Disjoint (swap (0 : Fin 11) 2 * swap 0 1) (swap 3 5 * swap 3 4) := by
    intro x
    revert x
    decide +kernel
  rw [e, Perm.Disjoint.cycleType_mul hd, h1.cycleType, h2.cycleType]
  rfl

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem sub_mem_range (g : GLV W) (x : W) :
    g x - x ∈ LinearMap.range ((g : W →ₗ[ZMod 2] W) - LinearMap.id) :=
  ⟨x, by simp⟩

theorem pow_sub_mem_range (g : GLV W) (u : W) (n : ℕ) :
    (g ^ n) u - u ∈ LinearMap.range ((g : W →ₗ[ZMod 2] W) - LinearMap.id) := by
  induction n with
  | zero => exact ⟨0, by rw [map_zero, pow_zero]; exact (sub_self u).symm⟩
  | succ n ih =>
    have h : (g ^ (n + 1)) u - u = (g ((g ^ n) u) - (g ^ n) u) + ((g ^ n) u - u) := by
      rw [pow_succ', LinearEquiv.mul_apply]
      abel
    rw [h]
    exact Submodule.add_mem _ (sub_mem_range g _) ih

theorem zpow_sub_mem_range (g : GLV W) (u : W) (n : ℤ) :
    (g ^ n) u - u ∈ LinearMap.range ((g : W →ₗ[ZMod 2] W) - LinearMap.id) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact pow_sub_mem_range g u m
  · have h := pow_sub_mem_range g ((g ^ (-(m : ℤ))) u) m
    have hgu : (g ^ m) ((g ^ (-(m : ℤ))) u) = u := by
      rw [← LinearEquiv.mul_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero]
      rfl
    rw [hgu] at h
    have h' := Submodule.neg_mem _ h
    rwa [neg_sub] at h'

theorem commSpace_zpowers (g : GLV W) :
    commSpace (Subgroup.zpowers g) ⊤ =
      LinearMap.range ((g : W →ₗ[ZMod 2] W) - LinearMap.id) := by
  apply le_antisymm
  · rw [commSpace, Submodule.span_le]
    rintro _ ⟨k, ⟨n, rfl⟩, u, -, rfl⟩
    exact zpow_sub_mem_range g u n
  · rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span ⟨g, Subgroup.mem_zpowers g, u, Submodule.mem_top, rfl⟩

theorem range_conj (t g : GLV W) :
    LinearMap.range (((t * g * t⁻¹ : GLV W) : W →ₗ[ZMod 2] W) - LinearMap.id) =
      (LinearMap.range ((g : W →ₗ[ZMod 2] W) - LinearMap.id)).map (t : W →ₗ[ZMod 2] W) := by
  ext w
  simp only [LinearMap.mem_range, Submodule.mem_map, LinearMap.sub_apply, LinearEquiv.coe_coe,
    LinearMap.id_apply]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨g (t⁻¹ u) - t⁻¹ u, ⟨t⁻¹ u, rfl⟩, ?_⟩
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    congr 1
    rw [← LinearEquiv.mul_apply t t⁻¹, mul_inv_cancel]
    rfl
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨t u, ?_⟩
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ← LinearEquiv.mul_apply t⁻¹ t, inv_mul_cancel]
    rfl

theorem finrank_range_conj [Finite W] (t g : GLV W) :
    Module.finrank (ZMod 2)
        (LinearMap.range (((t * g * t⁻¹ : GLV W) : W →ₗ[ZMod 2] W) - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range ((g : W →ₗ[ZMod 2] W) - LinearMap.id)) := by
  rw [range_conj]
  exact LinearEquiv.finrank_map_eq t _

theorem not_dvd_card_GL {k : ℕ} (hk : k ≤ 9) :
    ¬ 11 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  interval_cases k <;> decide

theorem eq_one_of_pow_eleven [Finite W] (hW : Module.finrank (ZMod 2) W ≤ 9) (x : GLV W)
    (hx : x ^ 11 = 1) : x = 1 := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let e : W ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) W) → ZMod 2) :=
    (Module.finBasis (ZMod 2) W).equivFun
  let ψ := L13Alt.glvEquiv e
  have hord : orderOf (ψ x) ∣ 11 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have hcard := orderOf_dvd_natCard (ψ x)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp hord with h | h
  · exact ψ.injective (by rw [orderOf_eq_one_iff.mp h, map_one])
  · rw [h] at hcard
    exact absurd hcard (not_dvd_card_GL hW)

theorem false_of_sub_mem [Finite W] (x : GLV W) (U : Submodule (ZMod 2) W)
    (hdim : Module.finrank (ZMod 2) U ≤ 9) (hxU : ∀ v, x v - v ∈ U) (h11 : x ^ 11 = 1)
    (hne : x ≠ 1) : False := by
  have hxinv : ∀ u ∈ U, x u ∈ U := fun u hu => by
    have := U.add_mem (hxU u) hu
    rwa [sub_add_cancel] at this
  have hx10 : ∀ u ∈ U, (x ^ 10) u ∈ U := by
    intro u hu
    induction 10 with
    | zero => exact hu
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply]
      exact hxinv _ ih
  let xU : GLV U :=
    { toFun := fun u => ⟨x (u : W), hxinv u u.2⟩
      invFun := fun u => ⟨(x ^ 10) (u : W), hx10 u u.2⟩
      map_add' := fun u v => Subtype.ext (map_add x (u : W) v)
      map_smul' := fun c u => Subtype.ext (map_smul x c (u : W))
      left_inv := fun u => Subtype.ext (by
        show (x ^ 10) (x (u : W)) = u
        rw [← LinearEquiv.mul_apply, ← pow_succ, h11]
        rfl)
      right_inv := fun u => Subtype.ext (by
        show x ((x ^ 10) (u : W)) = u
        rw [← LinearEquiv.mul_apply, ← pow_succ', h11]
        rfl) }
  have hpow : ∀ (n : ℕ) (u : U), ((xU ^ n) u : W) = (x ^ n) (u : W) := by
    intro n u
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, pow_succ', LinearEquiv.mul_apply, ← ih]
      rfl
  have hxU11 : xU ^ 11 = 1 := by
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    rw [hpow, h11]
    rfl
  have hxU1 := eq_one_of_pow_eleven (W := U) hdim xU hxU11
  have hfixU : ∀ u ∈ U, x u = u := fun u hu =>
    congrArg Subtype.val (LinearEquiv.congr_fun hxU1 ⟨u, hu⟩)
  have hvv : ∀ y : W, y + y = 0 := fun y => by
    nth_rewrite 2 [← ZModModule.neg_eq_self y]
    exact add_neg_cancel y
  have hx2 : x ^ 2 = 1 := by
    refine LinearEquiv.ext fun v => ?_
    show (x ^ 2) v = v
    have h1 := hfixU _ (hxU v)
    rw [map_sub] at h1
    rw [pow_two, LinearEquiv.mul_apply]
    calc x (x v) = (x (x v) - x v) + x v := by abel
      _ = (x v - v) + x v := by rw [h1]
      _ = (x v + x v) - v := by abel
      _ = v := by rw [hvv, zero_sub, ZModModule.neg_eq_self]
  apply hne
  have : x ^ 11 = x := by
    rw [show 11 = 2 * 5 + 1 from rfl, pow_succ, pow_mul, hx2, one_pow, one_mul]
  rw [← this, h11]

theorem false_of_rank_le_three [Finite W] (a₁ a₂ a₃ : GLV W)
    (h₁ : Module.finrank (ZMod 2) (LinearMap.range ((a₁ : W →ₗ[ZMod 2] W) - LinearMap.id)) ≤ 3)
    (h₂ : Module.finrank (ZMod 2) (LinearMap.range ((a₂ : W →ₗ[ZMod 2] W) - LinearMap.id)) ≤ 3)
    (h₃ : Module.finrank (ZMod 2) (LinearMap.range ((a₃ : W →ₗ[ZMod 2] W) - LinearMap.id)) ≤ 3)
    (h11 : (a₁ * a₂ * a₃) ^ 11 = 1) (hne : a₁ * a₂ * a₃ ≠ 1) : False := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  generalize hR₁ : LinearMap.range ((a₁ : W →ₗ[ZMod 2] W) - LinearMap.id) = R₁ at h₁
  generalize hR₂ : LinearMap.range ((a₂ : W →ₗ[ZMod 2] W) - LinearMap.id) = R₂ at h₂
  generalize hR₃ : LinearMap.range ((a₃ : W →ₗ[ZMod 2] W) - LinearMap.id) = R₃ at h₃
  have hmem : ∀ (a : GLV W) (R : Submodule (ZMod 2) W),
      LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id) = R → ∀ v, a v - v ∈ R := by
    rintro a R rfl v
    exact ⟨v, rfl⟩
  have hdim : Module.finrank (ZMod 2) ↥(R₁ ⊔ R₂ ⊔ R₃) ≤ 9 := by
    have e1 := Submodule.finrank_add_le_finrank_add_finrank (R₁ ⊔ R₂) R₃
    have e2 := Submodule.finrank_add_le_finrank_add_finrank R₁ R₂
    omega
  have hR1 : R₁ ≤ R₁ ⊔ R₂ ⊔ R₃ := le_sup_left.trans le_sup_left
  have hR2 : R₂ ≤ R₁ ⊔ R₂ ⊔ R₃ := le_sup_right.trans le_sup_left
  have hR3 : R₃ ≤ R₁ ⊔ R₂ ⊔ R₃ := le_sup_right
  have hinv : ∀ (a : GLV W) (R : Submodule (ZMod 2) W),
      LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id) = R → R ≤ R₁ ⊔ R₂ ⊔ R₃ →
        ∀ u ∈ R₁ ⊔ R₂ ⊔ R₃, a u ∈ R₁ ⊔ R₂ ⊔ R₃ := fun a R hR hle u hu => by
    have := (R₁ ⊔ R₂ ⊔ R₃).add_mem hu (hle (hmem a R hR u))
    rwa [add_sub_cancel] at this
  refine false_of_sub_mem (a₁ * a₂ * a₃) (R₁ ⊔ R₂ ⊔ R₃) hdim (fun v => ?_) h11 hne
  have hv : (a₁ * a₂ * a₃) v - v = a₁ (a₂ (a₃ v - v)) + a₁ (a₂ v - v) + (a₁ v - v) := by
    simp only [LinearEquiv.mul_apply, map_sub]
    abel
  rw [hv]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (hinv a₁ R₁ hR₁ hR1 _ (hinv a₂ R₂ hR₂ hR2 _ (hR3 (hmem a₃ R₃ hR₃ v))))
    (hinv a₁ R₁ hR₁ hR1 _ (hR2 (hmem a₂ R₂ hR₂ v)))) (hR1 (hmem a₁ R₁ hR₁ v))

end A11Aux

open A11Aux

theorem a11DoubleThreeCycle_holds : A11DoubleThreeCycle := by
  intro W _ _ _ H φ _ h hcyc
  by_contra hlt
  push Not at hlt
  obtain ⟨hg2, hg3, h11, hne⟩ := perm_facts
  obtain ⟨π, hπ⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_s1.trans hcyc.symm))
  have hev : ∀ g : Perm (Fin 11), sign g = 1 → π * g * π⁻¹ ∈ alternatingGroup (Fin 11) := by
    intro g hg
    rw [mem_alternatingGroup, map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one]
  let c2 : alternatingGroup (Fin 11) := ⟨π * g2 * π⁻¹, hev g2 sign_g2⟩
  let c3 : alternatingGroup (Fin 11) := ⟨π * g3 * π⁻¹, hev g3 sign_g3⟩
  let t2 : ↥H := φ.symm c2
  let t3 : ↥H := φ.symm c3
  let w : ↥H := h * (t2 * h * t2⁻¹) * (t3 * h * t3⁻¹)
  have hφw : ((φ w : alternatingGroup (Fin 11)) : Perm (Fin 11)) = π * (s1 * s2 * s3) * π⁻¹ := by
    have hh : ((φ h : alternatingGroup (Fin 11)) : Perm (Fin 11)) = π * s1 * π⁻¹ := hπ.symm
    simp only [w, t2, t3, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, hh, c2, c3]
    rw [← hg2, ← hg3]
    group
  have hw11 : w ^ 11 = 1 := by
    apply φ.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, hφw, conj_pow, h11, mul_one, mul_inv_cancel,
      Subgroup.coe_one]
  have hw1 : w ≠ 1 := by
    intro hw
    apply hne
    have := congrArg (fun z : ↥H => ((φ z : alternatingGroup (Fin 11)) : Perm (Fin 11))) hw
    simp only [hφw, map_one, Subgroup.coe_one] at this
    have h' := congrArg (fun z => π⁻¹ * z * π) this
    simpa [mul_assoc] using h'
  have h1 : Module.finrank (ZMod 2) (LinearMap.range
      (((h : GLV W) : W →ₗ[ZMod 2] W) - LinearMap.id)) ≤ 3 := by
    rw [← commSpace_zpowers]
    omega
  have hrk : ∀ t : ↥H, Module.finrank (ZMod 2) (LinearMap.range
      ((((t * h * t⁻¹ : ↥H) : GLV W) : W →ₗ[ZMod 2] W) - LinearMap.id)) ≤ 3 := by
    intro t
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [finrank_range_conj]
    exact h1
  refine false_of_rank_le_three (h : GLV W) ((t2 * h * t2⁻¹ : ↥H) : GLV W)
    ((t3 * h * t3⁻¹ : ↥H) : GLV W) h1 (hrk t2) (hrk t3) ?_ ?_
  · have := congrArg (fun z : ↥H => (z : GLV W)) hw11
    simpa [w] using this
  · intro h'
    apply hw1
    apply Subtype.ext
    simpa [w] using h'

end CFSG.CGT.Foote82
