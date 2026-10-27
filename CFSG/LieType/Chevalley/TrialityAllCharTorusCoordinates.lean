module

public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Lift

variable {τ : Tag} {K : Type} [Field K]

theorem cartanChar_mul (c c' : Fin τ.rank → Kˣ) :
    cartanChar (c * c') = cartanChar c * cartanChar c' := by
  funext l
  simp only [cartanChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem cartanChar_one : cartanChar (1 : Fin τ.rank → Kˣ) = 1 := by
  funext l
  simp [cartanChar]

theorem cartanChar_inv (c : Fin τ.rank → Kˣ) : cartanChar c⁻¹ = (cartanChar c)⁻¹ := by
  funext l
  simp only [cartanChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem cartanChar_mulSingle (i : Fin τ.rank) (u : Kˣ) :
    cartanChar (Pi.mulSingle i u) = fun l => u ^ τ.cartan i l := by
  funext l
  rw [cartanChar, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj,
    one_zpow]) (by simp), Pi.mulSingle_eq_same]

theorem exists_cartanChar_eq_of_mem_torusGroup
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    ∃ c : Fin τ.rank → Kˣ, h = rootDiagUnit τ (cartanChar c) := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, u⟩, rfl⟩ := hx
    refine ⟨Pi.mulSingle i u, ?_⟩
    rw [cartanChar_mulSingle]
    exact torusElt_eq_rootDiagUnit i u
  | one => exact ⟨1, by rw [cartanChar_one, rootDiagUnit_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c * c', by rw [cartanChar_mul, rootDiagUnit_mul]⟩
  | inv x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c⁻¹, by rw [cartanChar_inv, rootDiagUnit_inv]⟩

end Lift

section Coordinates

variable {K : Type} [Field K]

local notation "vec4" x₀:max x₁:max x₂:max x₃:max => d4Tuple x₀ x₁ x₂ x₃

theorem prod_D4 {M : Type*} [CommMonoid M] (f : Fin TwistTag.D4.tag.rank → M) :
    ∏ j, f j = f ⟨0, by decide⟩ * f ⟨1, by decide⟩ * f ⟨2, by decide⟩ * f ⟨3, by decide⟩ :=
  Fin.prod_univ_four f

theorem cartanChar_D4 (c : Fin TwistTag.D4.tag.rank → Kˣ) :
    cartanChar c = vec4 (c ⟨0, by decide⟩ ^ 2 * (c ⟨2, by decide⟩)⁻¹)
      (c ⟨1, by decide⟩ ^ 2 * (c ⟨2, by decide⟩)⁻¹)
      (c ⟨2, by decide⟩ ^ 2 * (c ⟨0, by decide⟩ * c ⟨1, by decide⟩ * c ⟨3, by decide⟩)⁻¹)
      (c ⟨3, by decide⟩ ^ 2 * (c ⟨2, by decide⟩)⁻¹) := by
  funext l
  rw [cartanChar, prod_D4]
  obtain ⟨n, hn⟩ := l
  have hn' : n < 4 := hn
  interval_cases n
  · change c ⟨0, by decide⟩ ^ (2 : ℤ) * c ⟨1, by decide⟩ ^ (0 : ℤ) * c ⟨2, by decide⟩ ^ (-1 : ℤ) *
      c ⟨3, by decide⟩ ^ (0 : ℤ) = c ⟨0, by decide⟩ ^ 2 * (c ⟨2, by decide⟩)⁻¹
    unit_arith
  · change c ⟨0, by decide⟩ ^ (0 : ℤ) * c ⟨1, by decide⟩ ^ (2 : ℤ) * c ⟨2, by decide⟩ ^ (-1 : ℤ) *
      c ⟨3, by decide⟩ ^ (0 : ℤ) = c ⟨1, by decide⟩ ^ 2 * (c ⟨2, by decide⟩)⁻¹
    unit_arith
  · change c ⟨0, by decide⟩ ^ (-1 : ℤ) * c ⟨1, by decide⟩ ^ (-1 : ℤ) *
      c ⟨2, by decide⟩ ^ (2 : ℤ) * c ⟨3, by decide⟩ ^ (-1 : ℤ) =
        c ⟨2, by decide⟩ ^ 2 * (c ⟨0, by decide⟩ * c ⟨1, by decide⟩ * c ⟨3, by decide⟩)⁻¹
    unit_arith
  · change c ⟨0, by decide⟩ ^ (0 : ℤ) * c ⟨1, by decide⟩ ^ (0 : ℤ) * c ⟨2, by decide⟩ ^ (-1 : ℤ) *
      c ⟨3, by decide⟩ ^ (2 : ℤ) = c ⟨3, by decide⟩ ^ 2 * (c ⟨2, by decide⟩)⁻¹
    unit_arith

end Coordinates

section Torus

variable {K : Type} [Field K] {σ : K ≃+* K}

local notation "vec4" x₀:max x₁:max x₂:max x₃:max => d4Tuple x₀ x₁ x₂ x₃
local notation "σu" => Units.map (RingHom.toMonoidHom (RingEquiv.toRingHom σ))

theorem sigma_eq_self_of_sq_eq (hσ : σ ^ 3 = 1) {A : K} (h : σ A ^ 2 = A ^ 2) : σ A = A := by
  have h3 : σ (σ (σ A)) = A := by rw [← ringEquiv_pow_three_apply, hσ]; rfl
  have hsq : (σ A - A) * (σ A + A) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hsq with h0 | h0
  · exact sub_eq_zero.1 h0
  · have hneg : σ A = -A := eq_neg_of_add_eq_zero_left h0
    have h2 : σ (σ A) = A := by rw [hneg, map_neg, hneg, neg_neg]
    have hAA : A + A = 0 := by
      have := h3
      rw [h2, hneg] at this
      linear_combination -this
    rw [hneg]
    linear_combination -hAA

theorem trialityTorusHom_injective_all
    (hσ : σ ^ 3 = 1) :
    Function.Injective (trialityTorusHom (K := K) σ) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hp
  rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, ← rootDiagUnit_one, ← vec4_one] at hp
  obtain ⟨h0, h1, h2, -⟩ := eq_of_vec4_eq (rootDiagUnit_injective hp)
  set A : K := (a : K) with hA
  set B : K := ((trialityFixedUnit K σ b : Kˣ) : K) with hB
  have hA0 : A ≠ 0 := a.ne_zero
  have hB0 : B ≠ 0 := (trialityFixedUnit K σ b).ne_zero
  have e0 : A ^ 2 = B := by
    have := congrArg Units.val h0
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_one] at this
    field_simp at this
    exact this
  have e1 : σ A ^ 2 = B := by
    have := congrArg Units.val h1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_one] at this
    field_simp at this
    exact this
  have hσA : σ A = A := sigma_eq_self_of_sq_eq hσ (by rw [e1, e0])
  have e2 : B ^ 2 = A * σ A * σ (σ A) := by
    have := congrArg Units.val h2
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_one] at this
    have hN : A * σ A * σ (σ A) ≠ 0 := by
      rw [hσA, hσA]
      exact mul_ne_zero (mul_ne_zero hA0 hA0) hA0
    field_simp at this
    exact this
  rw [hσA, hσA, ← e0] at e2
  have hA1 : A = 1 := by
    have h4 : A ^ 3 * (A - 1) = 0 := by linear_combination e2
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hA0
    · exact sub_eq_zero.1 h
  have ha : a = 1 := Units.ext hA1
  have hb : b = 1 := by
    refine Units.ext (Subtype.ext ?_)
    change B = 1
    rw [← e0, hA1, one_pow]
  rw [ha, hb]
  rfl

theorem sigma_eq_self_of_sq_eq_one {x : K} (hx : x ^ 2 = 1) : σ x = x := by
  have hx' : x * x = 1 := by rw [← pow_two]; exact hx
  rcases mul_self_eq_one_iff.1 hx' with h | h
  · rw [h, map_one]
  · rw [h, map_neg, map_one]

theorem triality_torus_relations {t0 t1 t2 t3 : K} (h0 : t0 ≠ 0) (h1 : t1 ≠ 0) (h2 : t2 ≠ 0)
    (h3 : t3 ≠ 0) (E1 : t1 ^ 2 * σ t2 = σ t0 ^ 2 * t2) (E3 : t3 ^ 2 * σ t2 = σ t1 ^ 2 * t2)
    (E0 : t0 ^ 2 * σ t2 = σ t3 ^ 2 * t2)
    (E2 : t2 ^ 2 * (σ t0 * σ t1 * σ t3) = σ t2 ^ 2 * (t0 * t1 * t3)) :
    σ t2 = t2 ∧ σ t0 ^ 2 = t1 ^ 2 ∧ σ t1 ^ 2 = t3 ^ 2 := by
  have hu2 : σ t2 ≠ 0 := (map_ne_zero σ).2 h2
  set P := t0 * t1 * t3 with hP
  set Q := σ t0 * σ t1 * σ t3 with hQ
  have hP0 : P ≠ 0 := mul_ne_zero (mul_ne_zero h0 h1) h3
  have hprod : Q ^ 2 * t2 ^ 3 = P ^ 2 * σ t2 ^ 3 := by
    rw [hQ, hP]
    linear_combination (σ t1 ^ 2 * σ t3 ^ 2 * t2 ^ 2) * E1 * (-1) +
      (t1 ^ 2 * σ t2 * σ t3 ^ 2 * t2) * E3 * (-1) + (t1 ^ 2 * σ t2 * t3 ^ 2 * σ t2) * E0 * (-1)
  have E2sq : t2 ^ 4 * Q ^ 2 = σ t2 ^ 4 * P ^ 2 := by
    linear_combination (t2 ^ 2 * Q + σ t2 ^ 2 * P) * E2
  have hk : P ^ 2 * t2 ^ 3 * σ t2 ^ 3 * (t2 - σ t2) = 0 := by
    linear_combination t2 ^ 3 * E2sq - t2 ^ 4 * hprod
  have hu : σ t2 = t2 := by
    rcases mul_eq_zero.1 hk with h | h
    · exfalso
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hP0) (pow_ne_zero 3 h2)) (pow_ne_zero 3 hu2) h
    · exact (sub_eq_zero.1 h).symm
  refine ⟨hu, ?_, ?_⟩
  · rw [hu] at E1
    exact (mul_right_cancel₀ h2 E1).symm
  · rw [hu] at E3
    exact (mul_right_cancel₀ h2 E3).symm

theorem triality_torus_solution {t0 t1 t3 : K} (h1 : t1 ≠ 0) (h3 : t3 ≠ 0)
    (hu0 : σ t0 ^ 2 = t1 ^ 2) (hu1 : σ t1 ^ 2 = t3 ^ 2) :
    (t0 * σ t1 * t3⁻¹) ^ 2 = t0 ^ 2 ∧ σ (t0 * σ t1 * t3⁻¹) ^ 2 = t1 ^ 2 ∧
      σ (σ (t0 * σ t1 * t3⁻¹)) ^ 2 = t3 ^ 2 ∧
      (t0 * σ t1 * t3⁻¹) * σ (t0 * σ t1 * t3⁻¹) * σ (σ (t0 * σ t1 * t3⁻¹)) = t0 * t1 * t3 := by
  set d1 := σ t0 / t1 with hd1
  set d3 := σ t1 / t3 with hd3
  have hd1sq : d1 ^ 2 = 1 := by rw [hd1, div_pow, hu0, div_self (pow_ne_zero 2 h1)]
  have hd3sq : d3 ^ 2 = 1 := by rw [hd3, div_pow, hu1, div_self (pow_ne_zero 2 h3)]
  have hσd1 : σ d1 = d1 := sigma_eq_self_of_sq_eq_one hd1sq
  have hσd3 : σ d3 = d3 := sigma_eq_self_of_sq_eq_one hd3sq
  have ht0 : σ t0 = d1 * t1 := by rw [hd1]; field_simp
  have ht1 : σ t1 = d3 * t3 := by rw [hd3]; field_simp
  have ha : t0 * σ t1 * t3⁻¹ = t0 * d3 := by rw [ht1]; field_simp
  have hσa : σ (t0 * σ t1 * t3⁻¹) = d1 * t1 * d3 := by rw [ha, map_mul, hσd3, ht0]
  have hσσa : σ (σ (t0 * σ t1 * t3⁻¹)) = d1 * (d3 * t3) * d3 := by
    rw [hσa, map_mul, map_mul, hσd1, ht1, hσd3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]
    linear_combination t0 ^ 2 * hd3sq
  · rw [hσa]
    linear_combination t1 ^ 2 * d3 ^ 2 * hd1sq + t1 ^ 2 * hd3sq
  · rw [hσσa]
    linear_combination t3 ^ 2 * d3 ^ 4 * hd1sq + t3 ^ 2 * (d3 ^ 2 + 1) * hd3sq
  · rw [hσσa, hσa, ha]
    linear_combination t0 * t1 * t3 * d3 ^ 4 * hd1sq + t0 * t1 * t3 * (d3 ^ 2 + 1) * hd3sq

theorem exists_trialityTorusHom_eq_all
    {h : ModGL TwistTag.D4.tag K}
    (hh : h ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) : ∃ p, trialityTorusHom σ p = h := by
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨c, rfl⟩ := exists_cartanChar_eq_of_mem_torusGroup hhT
  have hl := compat_of_twistHom_rootDiagUnit
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hhΓ).2
  rw [cartanChar_D4] at hl
  have p0 : TwistTag.D4.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have p1 : TwistTag.D4.perm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
  have p2 : TwistTag.D4.perm ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
  have p3 : TwistTag.D4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ := by decide
  have hl0 := hl ⟨0, by decide⟩
  have hl1 := hl ⟨1, by decide⟩
  have hl2 := hl ⟨2, by decide⟩
  have hl3 := hl ⟨3, by decide⟩
  rw [p0] at hl0
  rw [p1] at hl1
  rw [p2] at hl2
  rw [p3] at hl3
  set c0 := c ⟨0, by decide⟩ with hc0
  set c1 := c ⟨1, by decide⟩ with hc1
  set c2 := c ⟨2, by decide⟩ with hc2
  set c3 := c ⟨3, by decide⟩ with hc3
  have q0 : c1 ^ 2 * c2⁻¹ = σu (c0 ^ 2 * c2⁻¹) := hl0
  have q1 : c3 ^ 2 * c2⁻¹ = σu (c1 ^ 2 * c2⁻¹) := hl1
  have q2 : c2 ^ 2 * (c0 * c1 * c3)⁻¹ = σu (c2 ^ 2 * (c0 * c1 * c3)⁻¹) := hl2
  have q3 : c0 ^ 2 * c2⁻¹ = σu (c3 ^ 2 * c2⁻¹) := hl3
  set t0 : K := (c0 : K) with ht0
  set t1 : K := (c1 : K) with ht1
  set t2 : K := (c2 : K) with ht2
  set t3 : K := (c3 : K) with ht3
  have h0 : t0 ≠ 0 := c0.ne_zero
  have h1 : t1 ≠ 0 := c1.ne_zero
  have h2 : t2 ≠ 0 := c2.ne_zero
  have h3 : t3 ≠ 0 := c3.ne_zero
  have hu0 : σ t0 ≠ 0 := (map_ne_zero σ).2 h0
  have hu1 : σ t1 ≠ 0 := (map_ne_zero σ).2 h1
  have hu2 : σ t2 ≠ 0 := (map_ne_zero σ).2 h2
  have hu3 : σ t3 ≠ 0 := (map_ne_zero σ).2 h3
  have tok : ∀ {x y : Kˣ}, x = y → (x : K) = y := fun h => congrArg Units.val h
  have E1 : t1 ^ 2 * σ t2 = σ t0 ^ 2 * t2 := by
    have := tok q0
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      coe_units_map_sigma, map_mul, map_pow, map_inv₀] at this
    field_simp at this
    linear_combination this
  have E3 : t3 ^ 2 * σ t2 = σ t1 ^ 2 * t2 := by
    have := tok q1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      coe_units_map_sigma, map_mul, map_pow, map_inv₀] at this
    field_simp at this
    linear_combination this
  have E0 : t0 ^ 2 * σ t2 = σ t3 ^ 2 * t2 := by
    have := tok q3
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      coe_units_map_sigma, map_mul, map_pow, map_inv₀] at this
    field_simp at this
    linear_combination this
  have E2 : t2 ^ 2 * (σ t0 * σ t1 * σ t3) = σ t2 ^ 2 * (t0 * t1 * t3) := by
    have := tok q2
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      coe_units_map_sigma, map_mul, map_pow, map_inv₀] at this
    field_simp at this
    linear_combination this
  obtain ⟨hσt2, hσt0, hσt1⟩ := triality_torus_relations h0 h1 h2 h3 E1 E3 E0 E2
  obtain ⟨g0, g1, g3, gN⟩ := triality_torus_solution (σ := σ) h1 h3 hσt0 hσt1
  have hbmem : t2 ∈ trialityFixedField K σ.toRingHom := (mem_trialityFixedField).2 hσt2
  set b : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨t2, hbmem⟩ fun h => h2 (congrArg Subtype.val h) with hb
  have hbB : ((trialityFixedUnit K σ b : Kˣ) : K) = t2 := rfl
  set a : Kˣ := c0 * σu c1 * c3⁻¹ with ha
  have haA : ((a : Kˣ) : K) = t0 * σ t1 * t3⁻¹ := by
    simp only [ha, Units.val_mul, Units.val_inv_eq_inv_val, coe_units_map_sigma, ← ht0, ← ht1,
      ← ht3]
  refine ⟨(a, b), ?_⟩
  rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, cartanChar_D4]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> refine Units.ext ?_ <;>
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      coe_units_map_sigma, hbB, haA]
  · rw [g0]
  · rw [g1]
  · rw [gN]
    ring
  · rw [g3]

theorem orbitH_mul_orbitH_eq_trialityTorusHom
    (a' : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ)
    (b' : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ)
    (b : (trialityFixedField K σ.toRingHom)ˣ)
    (hb : ((trialityFixedUnit K σ b : Kˣ) : K) =
      ((b' : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) : K)) :
    (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ a' : ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ b' =
      trialityTorusHom σ (orbitFieldUnit TwistTag.D4 σ.toRingHom a', b) := by
  have hbB : trialityFixedUnit K σ b = orbitFieldUnit TwistTag.D4 σ.toRingHom b' := Units.ext hb
  rw [← list_prod_orbitH_d4Pair, list_prod_orbitH_eq_rootDiagUnit, compatDiag_D4,
    trialityTorusHom_apply, trialityOuter_mul_middle_eq, hbB]
  refine (congrArg (rootDiagUnit TwistTag.D4.tag) (cartanChar_D4 _)).trans ?_
  exact congrArg _ (vec4_eq rfl rfl (mul_comm _ _) rfl)

end Torus

section Main

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def trialityOuterParam (hσ : σ ^ 3 = 1) (a : Kˣ) :
    (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ :=
  Units.mk0 ⟨a, by
    rw [orbitField_D4_zero_eq_top σ fun c => by rw [← ringEquiv_pow_three_apply, hσ]; rfl]
    trivial⟩ fun h => a.ne_zero (congrArg Subtype.val h)

@[expose] def trialityMiddleParam (b : (trialityFixedField K σ.toRingHom)ˣ) :
    (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ :=
  Units.mk0 ⟨(trialityFixedUnit K σ b : K), (mem_orbitField_D4_one σ).2 (sigma_trialityFixedUnit b)⟩
    fun h => (trialityFixedUnit K σ b).ne_zero (congrArg Subtype.val h)

theorem orbitFieldUnit_trialityOuterParam (hσ : σ ^ 3 = 1) (a : Kˣ) :
    orbitFieldUnit TwistTag.D4 σ.toRingHom (trialityOuterParam hσ a) = a :=
  Units.ext rfl

theorem trialityTorusHom_eq_orbitH
    (hσ : σ ^ 3 = 1) (a : Kˣ)
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ (a, b) =
      (orbitH TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ (trialityOuterParam hσ a) :
        ModGL TwistTag.D4.tag K) *
        orbitH TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ (trialityMiddleParam b) := by
  rw [orbitH_mul_orbitH_eq_trialityTorusHom (trialityOuterParam hσ a) (trialityMiddleParam b) b
    rfl, orbitFieldUnit_trialityOuterParam]

theorem trialityTorusHom_mem_graphFixedRootGroup
    (hσ : σ ^ 3 = 1)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ p ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  obtain ⟨a, b⟩ := p
  rw [trialityTorusHom_eq_orbitH hσ]
  exact mul_mem (orbitH_mem_graphFixedRootGroup _ _ _ _) (orbitH_mem_graphFixedRootGroup _ _ _ _)

theorem graphFixedTorus_eq_graphFixedRootTorus_D4
    (hσ : σ ^ 3 = 1) :
    graphFixedTorus TwistTag.D4 K σ.toRingHom = graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  rw [graphFixedRootTorus, eq_comm, inf_eq_left]
  intro h hh
  obtain ⟨p, rfl⟩ := exists_trialityTorusHom_eq_all hh
  exact trialityTorusHom_mem_graphFixedRootGroup hσ p

theorem orbitH_one'
    (a : Fin TwistTag.D4.foldedTag.rank) :
    (orbitH TwistTag.D4 K σ.toRingHom a 1 : ModGL TwistTag.D4.tag K) = 1 := by
  rw [orbitH, mul_inv_cancel]
  rfl

theorem eq_HSL_of_smul_one {F : Type} [Field F] {g : SL2 F} {l : Fˣ} (hl : (l : F) ^ 2 = 1)
    (hg : (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    g = HSL l := by
  have hinv : ((l⁻¹ : Fˣ) : F) = l := by
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hl)
  refine Subtype.ext ?_
  rw [hg, coe_HSL, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem HSL_one {F : Type} [Field F] : HSL (1 : Fˣ) = 1 :=
  Subtype.ext (by
    rw [coe_HSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp)

theorem orbitRankOneHom_injective_D4
    (hσ : σ ^ 3 = 1) (a : Fin TwistTag.D4.foldedTag.rank) :
    Function.Injective (orbitRankOneHom TwistTag.D4 K σ.toRingHom a) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨l, hl2, hgl⟩ := eq_smul_one_of_mem_ker_orbitRankOneHom (MonoidHom.mem_ker.2 hg)
  have hgH := eq_HSL_of_smul_one hl2 hgl
  rw [hgH, orbitRankOneHom_HSL] at hg
  rw [hgH]
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n
  ·
    have e := orbitH_mul_orbitH_eq_trialityTorusHom (σ := σ) l
      (1 : (orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩)ˣ) 1
      (by simp only [map_one, Units.val_one, OneMemClass.coe_one])
    rw [hg, orbitH_one', one_mul, ← map_one (trialityTorusHom σ)] at e
    have h1 := (Prod.ext_iff.1 (trialityTorusHom_injective_all hσ e.symm)).1
    have hl : l = 1 := Units.ext (Subtype.ext (congrArg Units.val h1))
    rw [hl, HSL_one]
  ·
    set b : (trialityFixedField K σ.toRingHom)ˣ := Units.mk0
      ⟨(l : K), (mem_orbitField_D4_one σ).1 (l : orbitField TwistTag.D4 K σ.toRingHom
        ⟨1, by decide⟩).2⟩ fun h => l.ne_zero (Subtype.ext (congrArg Subtype.val h))
    have e := orbitH_mul_orbitH_eq_trialityTorusHom (σ := σ)
      (1 : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ) l b rfl
    have h01 : orbitFieldUnit TwistTag.D4 σ.toRingHom
        (1 : (orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩)ˣ) = 1 := Units.ext rfl
    rw [hg, orbitH_one', one_mul, h01, ← map_one (trialityTorusHom σ)] at e
    have h1 : b = 1 := (Prod.ext_iff.1 (trialityTorusHom_injective_all hσ e.symm)).2
    have h1' : ((b : trialityFixedField K σ.toRingHom) : K) = 1 := by rw [h1]; rfl
    have hl : l = 1 := Units.ext (Subtype.ext h1')
    rw [hl, HSL_one]

end Main

theorem triality_all_characteristic_faithful_torus_coordinates
    (K : Type) [Field K]
    (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    graphFixedTorus TwistTag.D4 K σ.toRingHom = graphFixedRootTorus TwistTag.D4 K σ.toRingHom ∧
    (∃ e : (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) ≃*
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ a b, (e (a, b) : ModGL TwistTag.D4.tag K) =
        trialityOuterTorus K σ a * trialityMiddleTorus K σ b) ∧
    orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ = trialityFixedField K σ.toRingHom ∧
    (∀ a : Fin TwistTag.D4.foldedTag.rank,
      (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range ≤
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      Function.Injective (orbitRankOneHom TwistTag.D4 K σ.toRingHom a)) ∧
    (∀ a : Kˣ, trialityOuterRep K * trialityOuterTorus K σ a * (trialityOuterRep K)⁻¹ =
      trialityOuterTorus K σ a⁻¹) ∧
    (∀ b : (trialityFixedField K σ.toRingHom)ˣ,
      trialityMiddleRep K * trialityMiddleTorus K σ b * (trialityMiddleRep K)⁻¹ =
        trialityMiddleTorus K σ b⁻¹) ∧
    (∀ b : (trialityFixedField K σ.toRingHom)ˣ,
      trialityOuterRep K * trialityMiddleTorus K σ b * (trialityOuterRep K)⁻¹ =
        trialityMiddleTorus K σ b * trialityOuterTorus K σ (trialityFixedUnit K σ b)) ∧
    ∀ a : Kˣ, trialityMiddleRep K * trialityOuterTorus K σ a * (trialityMiddleRep K)⁻¹ =
      trialityOuterTorus K σ a * trialityMiddleTorus K σ (trialityNorm σ hσ a) := by
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by rw [← ringEquiv_pow_three_apply, hσ]; rfl
  have hH := graphFixedTorus_eq_graphFixedRootTorus_D4 (K := K) hσ
  let f : Kˣ × (trialityFixedField K σ.toRingHom)ˣ →*
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    (trialityTorusHom σ).codRestrict _ fun p => by
      rw [← hH]
      exact trialityTorusHom_mem_graphFixedTorus hσ p
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => trialityTorusHom_injective_all hσ (congrArg Subtype.val hpq),
      fun h => ?_⟩
    have hh : (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
      rw [hH]
      exact h.2
    obtain ⟨p, hp⟩ := exists_trialityTorusHom_eq_all hh
    exact ⟨p, Subtype.ext hp⟩
  have hL2 : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =
      trialityFixedField K σ.toRingHom := by
    ext c
    rw [mem_orbitField_D4_one σ, mem_trialityFixedField]
    rfl
  refine ⟨hH, ⟨MulEquiv.ofBijective f hf, fun a b => rfl⟩, orbitField_D4_zero_eq_top σ h3, hL2,
    fun a => ⟨?_, orbitRankOneHom_injective_D4 hσ a⟩, trialityOuterRep_conj_outer,
    trialityMiddleRep_conj_middle, trialityOuterRep_conj_middle, trialityMiddleRep_conj_outer hσ⟩
  rw [orbitRankOneHom_range]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (orbitX_mem_graphFixedPosUnipotent _ _ a c)
  · exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
      (orbitY_mem_graphFixedNegUnipotent _ _ a c)

end CFSG.LieType.Chevalley
