module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometrySpaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.PSpSmall

open Module CFSG.ComponentClassification.CatalogueBUnitaryIsometry
open CFSG.ComponentClassification.CatalogueBUnitaryTwo

theorem exists_orderOf_eq_eight_of_orderOf_eq_sixteen {G F : Type*} [Group G] [Finite G]
    [Group F] (φ : G →* F) (hker : Nat.card φ.ker ≤ 2) {x : G} (hx : orderOf x = 16) :
    ∃ y : F, orderOf y = 8 := by
  have hodvd : orderOf (φ x) ∣ 16 := hx ▸ orderOf_map_dvd φ x
  have ho0 : orderOf (φ x) ≠ 0 := (Nat.pos_of_dvd_of_pos hodvd (by norm_num)).ne'
  have hxo : x ^ orderOf (φ x) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hord : orderOf (x ^ orderOf (φ x)) = 16 / orderOf (φ x) := by
    rw [orderOf_pow' _ ho0, hx, Nat.gcd_eq_right hodvd]
  have hle : 16 / orderOf (φ x) ≤ 2 := by
    have h1 : orderOf (⟨x ^ orderOf (φ x), hxo⟩ : φ.ker) ∣ Nat.card φ.ker :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at h1
    exact (Nat.le_of_dvd Nat.card_pos h1).trans hker
  have key : ∀ o : ℕ, 0 < o → o ∣ 16 → 16 / o ≤ 2 → o = 8 ∨ o = 16 := by
    intro o ho h1 h2
    have : o ≤ 16 := Nat.le_of_dvd (by norm_num) h1
    interval_cases o <;> omega
  rcases key _ (Nat.pos_of_ne_zero ho0) hodvd hle with h | h
  · exact ⟨φ x, h⟩
  · refine ⟨φ x ^ 2, ?_⟩
    rw [orderOf_pow' _ (by norm_num), h]
    norm_num

theorem two_pow_dvd_card_range_of_card_ker_le_two {G F : Type*} [Group G] [Finite G] [Group F]
    (φ : G →* F) (hker : Nat.card φ.ker ≤ 2) {k : ℕ} (hk : 2 ^ (k + 1) ∣ Nat.card G) :
    2 ^ k ∣ Nat.card φ.range := by
  have hcard : Nat.card G = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  rw [hcard] at hk
  interval_cases h : Nat.card φ.ker
  · rw [mul_one] at hk
    exact (pow_dvd_pow 2 (Nat.le_succ k)).trans hk
  · rw [pow_succ] at hk
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hk

theorem two_pow_dvd_card_of_card_ker_le_two {G F : Type*} [Group G] [Finite G] [Group F] [Finite F]
    (φ : G →* F) (hker : Nat.card φ.ker ≤ 2) {k : ℕ} (hk : 2 ^ (k + 1) ∣ Nat.card G) :
    2 ^ k ∣ Nat.card F :=
  (two_pow_dvd_card_range_of_card_ker_le_two φ hker hk).trans (Subgroup.card_subgroup_dvd_card _)

section Torus

variable {E : Type} [Field E] (sigma : E ≃+* E)

@[expose] def torusDiagEquiv (a : Eˣ) : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E) :=
  LinearEquiv.piCongrRight
    ![LinearEquiv.smulOfUnit a, LinearEquiv.smulOfUnit (Units.map sigma.toRingHom.toMonoidHom a)⁻¹]

theorem torusDiagEquiv_apply_zero (a : Eˣ) (x : Fin 2 → E) : torusDiagEquiv sigma a x 0 = a * x 0 :=
  rfl

theorem torusDiagEquiv_apply_one (a : Eˣ) (x : Fin 2 → E) :
    torusDiagEquiv sigma a x 1 = (sigma (a : E))⁻¹ * x 1 := by
  change (((Units.map sigma.toRingHom.toMonoidHom a)⁻¹ : Eˣ) : E) * x 1 = _
  simp

theorem torusDiagEquiv_mem (hsigma : sigma ^ 2 = 1) (a : Eˣ) :
    torusDiagEquiv sigma a ∈ isometryGroup (hyperbolicForm sigma) := by
  intro x y
  have hinv : sigma (sigma (a : E)) = a := CatalogueBUnitaryNorm.involutive sigma hsigma _
  have ha : (a : E) ≠ 0 := a.ne_zero
  have hs : sigma (a : E) ≠ 0 := by simpa using ha
  rw [hyperbolicForm_apply, hyperbolicForm_apply, torusDiagEquiv_apply_zero,
    torusDiagEquiv_apply_one, torusDiagEquiv_apply_zero, torusDiagEquiv_apply_one, map_mul,
    map_mul, map_inv₀, hinv]
  field_simp

theorem torusDiagEquiv_one : torusDiagEquiv sigma 1 = LinearEquiv.refl E (Fin 2 → E) := by
  ext x i
  fin_cases i <;> simp [torusDiagEquiv_apply_zero, torusDiagEquiv_apply_one]

theorem torusDiagEquiv_mul (a b : Eˣ) :
    torusDiagEquiv sigma (a * b) = torusDiagEquiv sigma a * torusDiagEquiv sigma b := by
  ext x i
  fin_cases i
  · simp [torusDiagEquiv_apply_zero, mul_assoc]
  · simp [torusDiagEquiv_apply_one, mul_assoc, mul_comm, mul_left_comm]

@[expose] def unitaryTorus (hsigma : sigma ^ 2 = 1) :
    Eˣ →* isometryGroup (hyperbolicForm sigma) where
  toFun a := ⟨torusDiagEquiv sigma a, torusDiagEquiv_mem sigma hsigma a⟩
  map_one' := Subtype.ext (torusDiagEquiv_one sigma)
  map_mul' a b := Subtype.ext (torusDiagEquiv_mul sigma a b)

theorem unitaryTorus_injective (hsigma : sigma ^ 2 = 1) :
    Function.Injective (unitaryTorus sigma hsigma) := by
  intro a b hab
  have h0 := congrArg (fun g : isometryGroup (hyperbolicForm sigma) =>
    g.1 (Pi.single 0 1) 0) hab
  exact Units.ext (by simpa [unitaryTorus, torusDiagEquiv_apply_zero] using h0)

variable {sigma} {W : Type} [AddCommGroup W] [Module E W]

@[expose] def unitaryTorusIn (hsigma : sigma ^ 2 = 1) (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E)
    (B : (Fin 2 → E) ≃ₗ[E] W) (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) :
    Eˣ →* isometryGroup h :=
  (formIsometryGroupEquiv (hyperbolicForm sigma) h B hB).toMonoidHom.comp
    (unitaryTorus sigma hsigma)

theorem unitaryTorusIn_injective (hsigma : sigma ^ 2 = 1) (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E)
    (B : (Fin 2 → E) ≃ₗ[E] W) (hB : ∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) :
    Function.Injective (unitaryTorusIn hsigma h B hB) :=
  (formIsometryGroupEquiv (hyperbolicForm sigma) h B hB).injective.comp
    (unitaryTorus_injective sigma hsigma)

theorem exists_orderOf_eq_sixteen_units [Finite E] (hE : Nat.card E = (3 ^ 2) ^ 2) :
    ∃ a : Eˣ, orderOf a = 16 := by
  have h80 : Nat.card Eˣ = 80 := by
    rw [Nat.card_units, hE]
    norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  rw [h80] at hg
  refine ⟨g ^ 5, ?_⟩
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]

variable [FiniteDimensional E W]

theorem exists_orderOf_eq_sixteen_isometryGroup [Finite E] (hE : Nat.card E = (3 ^ 2) ^ 2)
    (hW : finrank E W = 2) (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ x : isometryGroup h, orderOf x = 16 := by
  obtain ⟨B, hB⟩ := exists_hyperbolic_isometry sigma h hsym hnd hsigma hne hW
  obtain ⟨a, ha⟩ := exists_orderOf_eq_sixteen_units (E := E) hE
  exact ⟨unitaryTorusIn hsigma h B hB a, by
    rw [orderOf_injective _ (unitaryTorusIn_injective hsigma h B hB) a, ha]⟩

theorem exists_orderOf_eq_sixteen_of_mulEquiv [Finite E] (hE : Nat.card E = (3 ^ 2) ^ 2)
    (hW : finrank E W = 2) (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) {G : Type} [Group G]
    (e : G ≃* isometryGroup h) : ∃ x : G, orderOf x = 16 := by
  obtain ⟨x, hx⟩ := exists_orderOf_eq_sixteen_isometryGroup hE hW h hsym hnd hsigma hne
  exact ⟨e.symm x, by rw [MulEquiv.orderOf_eq, hx]⟩

end Torus

end CFSG.ComponentClassification.CatFC.PSpSmall
