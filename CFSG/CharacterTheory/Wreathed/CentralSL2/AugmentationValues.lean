module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ActionKernel
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.CharacterTheory.PermutationCharacterOrbits

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section FixedPoints

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem fixedPointCount_semilinear [Finite F]
    (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) h =
      (Nat.card {x // semilinearAction F b m hm heven Sigma hSigma h x = x} : ℂ) := rfl

theorem fixedPointCount_linear [Finite F] (h2 : (2 : F) ≠ 0) (X : SpecialLinearGroup (Fin 2) F)
    (j : ZMod (2 * m)) :
    let C := SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
        ⟨quotientClass F b m hm heven X j, 1⟩ =
      if ∃ c : Fˣ, C = GeneralLinearGroup.scalar (Fin 2) c then (Nat.card F + 1 : ℂ)
      else (sqrtCount (Matrix.trace C.val ^ 2 - 4 * Matrix.det C.val) : ℂ) := by
  intro C
  rw [fixedPointCount_semilinear, semilinearAction_mk, projAction_quotientClass]
  have hone : fieldExtension F ((1 : Sigma) : F ≃+* F) = 1 := by
    refine Equiv.ext fun x => ?_
    cases x <;> rfl
  simp only [hone, mul_one]
  split_ifs with hC
  · obtain ⟨c, hc⟩ := hC
    change (Nat.card {x // coordinateGLAction F C x = x} : ℂ) = _
    rw [hc, coordinateGLAction_scalar]
    simp only [Equiv.Perm.one_apply]
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial), Nat.card_eq_fintype_card,
      Fintype.card_option, Nat.card_eq_fintype_card]
    push_cast
    rfl
  · change (Nat.card {x // coordinateGLAction F C x = x} : ℂ) = _
    rw [card_fixed_coordinateGLAction h2 C hC]

theorem mem_fixedSubfield_zpowers_iff (σ : F ≃+* F) (y : F) :
    y ∈ FixedPoints.subfield (Subgroup.zpowers σ) F ↔ σ y = y := by
  rw [CFSG.Semidihedral.FixedFieldData.mem_fixedSubfield_iff]
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro hσ a
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (F ≃+* F) y := by
      rw [Subgroup.zpowers_le]
      exact hσ
    exact hle a.2

theorem fixedPointCount_field [Finite F] {p f : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ f)
    (σ : Sigma) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
        ⟨1, σ⟩ = 1 + (p : ℂ) ^ (f / orderOf σ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  rw [fixedPointCount_semilinear, semilinearAction_mk, map_one, one_mul, card_fixed_option]
  simp only [fieldExtension_none, fieldExtension_some, Option.some.injEq, ite_true]
  have hcardA : Nat.card (Subgroup.zpowers (σ : F ≃+* F)) = orderOf σ := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
  have h := CFSG.Semidihedral.FixedFieldData.fixedSubfield_card p f F hcard
    (Subgroup.zpowers (σ : F ≃+* F))
  rw [hcardA] at h
  have hequiv : Nat.card {y : F // (σ : F ≃+* F) y = y} =
      Nat.card (FixedPoints.subfield (Subgroup.zpowers (σ : F ≃+* F)) F) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y =>
      (mem_fixedSubfield_zpowers_iff F (σ : F ≃+* F) y).symm)
  rw [hequiv, h]
  push_cast
  ring

end FixedPoints

section CyclicField

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem fixed_of_mul_apply_eq (σ : F ≃+* F) (hσodd : Odd (orderOf σ)) {c : F} (hc : σ c = c)
    (hc0 : c ≠ 0) {y : F} (hy : y * σ y = c) : σ y = y := by
  have hσy : σ y ≠ 0 := by
    intro h
    rw [h, mul_zero] at hy
    exact hc0 hy.symm
  have hsq : σ (σ y) = y := by
    have h1 : σ y * σ (σ y) = c := by rw [← map_mul, hy, hc]
    have h2 : σ y * σ (σ y) = σ y * y := by rw [h1, ← hy, mul_comm]
    exact mul_left_cancel₀ hσy h2
  have hpow : ∀ n : ℕ, (σ ^ (2 * n)) y = y := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add, RingAut.mul_apply, ih, pow_two,
        RingAut.mul_apply, hsq]
  obtain ⟨k, hk⟩ := hσodd
  have hσ : σ = σ ^ (2 * (k + 1)) := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, ← hk, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hσ]
  exact hpow (k + 1)

theorem isSquare_neg_fixedField [Finite F] (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b) (σ : F ≃+* F)
    (hσb : σ (b : F) = b) (hσodd : Odd (orderOf σ)) :
    (∃ c : F, σ c = c ∧ c * c = -b) ↔ Nat.card F % 4 = 3 := by
  set F₀ := FixedPoints.subfield (Subgroup.zpowers σ) F with hF₀
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hbF₀ : (b : F) ∈ F₀ := (mem_fixedSubfield_zpowers_iff F σ _).mpr hσb
  set b₀ : F₀ := ⟨b, hbF₀⟩ with hb₀
  have hb₀sq : ¬ IsSquare b₀ := by
    rintro ⟨z, hz⟩
    apply hb
    have hz' : (b : F) = (z : F) * z := congrArg Subtype.val hz
    have hz0 : (z : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hz'
      exact b.ne_zero hz'
    exact ⟨Units.mk0 (z : F) hz0, Units.ext (by simp [hz'])⟩
  have hb₀0 : b₀ ≠ 0 := by
    intro h
    exact b.ne_zero (congrArg Subtype.val h)
  have hsq : (∃ c : F, σ c = c ∧ c * c = -b) ↔ IsSquare (-b₀) := by
    constructor
    · rintro ⟨c, hc, hcc⟩
      refine ⟨⟨c, (mem_fixedSubfield_zpowers_iff F σ c).mpr hc⟩, ?_⟩
      apply Subtype.ext
      simp [hb₀, hcc]
    · rintro ⟨z, hz⟩
      refine ⟨z, (mem_fixedSubfield_zpowers_iff F σ z).mp z.2, ?_⟩
      have := congrArg Subtype.val hz
      simpa [hb₀] using this.symm
  rw [hsq]
  have hneg : IsSquare (-b₀) ↔ ¬ IsSquare (-1 : F₀) := by
    have hchib : quadraticChar F₀ b₀ = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hb₀sq
    have hmul : quadraticChar F₀ (-b₀) = quadraticChar F₀ (-1) * quadraticChar F₀ b₀ := by
      rw [← map_mul, neg_one_mul]
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hb₀0),
      ← quadraticChar_neg_one_iff_not_isSquare, hmul, hchib]
    constructor
    · intro h
      linear_combination -h
    · intro h
      rw [h]
      ring
  rw [hneg, FiniteField.isSquare_neg_one_iff, not_not]
  have hpow : Nat.card F = Nat.card F₀ ^ orderOf σ := by
    have h := CFSG.Semidihedral.FixedFieldData.nat_card_eq_fixedSubfield_card_pow F
      (Subgroup.zpowers σ)
    rwa [Nat.card_zpowers] at h
  have hq0odd : Odd (Nat.card F₀) := by
    have hFodd : Odd (Nat.card F) := by
      have : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card, Nat.odd_iff]
      exact FiniteField.odd_card_of_char_ne_two (by
        intro h
        apply h2
        have h' := ringChar.Nat.cast_ringChar (R := F)
        rw [h, Nat.cast_ofNat] at h'
        exact h')
    rw [hpow] at hFodd
    have : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
      (fun _ _ h => RingEquiv.ext (congrFun h))
    exact (Nat.odd_pow_iff (orderOf_pos σ).ne').mp hFodd
  have h8 := CFSG.Semidihedral.FixedFieldData.odd_power_mod_eight hq0odd hσodd
  rw [← Nat.card_eq_fintype_card, hpow]
  omega

theorem coordJ_some (z : F) :
    coordJ F b (some z) = if z = 0 then none else some (-(b : F) / z) := by
  have hJ10 : (nonsquareMatrix F b).val 1 0 = 1 := by simp [nonsquareMatrix_val]
  have hJ00 : (nonsquareMatrix F b).val 0 0 = 0 := by simp [nonsquareMatrix_val]
  have hJ01 : (nonsquareMatrix F b).val 0 1 = -(b : F) := by simp [nonsquareMatrix_val]
  have hJ11 : (nonsquareMatrix F b).val 1 1 = 0 := by simp [nonsquareMatrix_val]
  rw [coordJ]
  split_ifs with hz
  · exact coordinateGLAction_finite_denominator_zero F _ z (by rw [hJ10, hJ11, hz]; ring)
  · rw [coordinateGLAction_finite F _ z (by rw [hJ10, hJ11]; simpa using hz), hJ00, hJ01, hJ10,
      hJ11]
    congr 1
    ring

theorem coordJ_none : coordJ F b none = some 0 := by
  rw [coordJ, coordinateGLAction_infinity F _ (by simp [nonsquareMatrix_val])]
  simp [nonsquareMatrix_val]

theorem fixedPointCount_cyclic_field [Finite F] (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b) (σ : Sigma)
    (hσodd : Odd (orderOf σ)) :
    fixedPointCount (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F)
        ⟨cyclicGenerator F b m hm heven, σ⟩ = if Nat.card F % 4 = 3 then 2 else 0 := by
  have hσb : (σ : F ≃+* F) (b : F) = b := hSigma σ σ.2
  have hσodd' : Odd (orderOf (σ : F ≃+* F)) := by rwa [Subgroup.orderOf_coe]
  rw [fixedPointCount_semilinear, semilinearAction_mk, projAction_cyclicGenerator,
    card_fixed_option]
  have hnone : (coordJ F b * fieldExtension F (σ : F ≃+* F)) none ≠ none := by
    rw [Equiv.Perm.mul_apply, fieldExtension_none, coordJ_none]
    exact Option.some_ne_none _
  rw [ite_eq_right hnone, zero_add]
  have hnegb : (σ : F ≃+* F) (-(b : F)) = -(b : F) := by rw [map_neg, hσb]
  have hnegb0 : -(b : F) ≠ 0 := neg_ne_zero.mpr b.ne_zero
  have hpred : ∀ y : F, (coordJ F b * fieldExtension F (σ : F ≃+* F)) (some y) = some y ↔
      (σ : F ≃+* F) y = y ∧ y * y = -b := by
    intro y
    rw [Equiv.Perm.mul_apply, fieldExtension_some, coordJ_some]
    constructor
    · intro h
      split_ifs at h with hz
      have hmul : y * (σ : F ≃+* F) y = -b := by
        have h' := Option.some.inj h
        field_simp at h'
        linear_combination -h'
      have hfix := fixed_of_mul_apply_eq F (σ : F ≃+* F) hσodd' hnegb hnegb0 hmul
      refine ⟨hfix, ?_⟩
      rw [← hmul, hfix]
    · rintro ⟨hfix, hyy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hyy
        exact hnegb0 hyy.symm
      rw [hfix, ite_eq_right hy0]
      congr 1
      field_simp
      linear_combination -hyy
  rw [Nat.card_congr (Equiv.subtypeEquivRight hpred)]
  split_ifs with hq
  · obtain ⟨c, hc, hcc⟩ := (isSquare_neg_fixedField F b h2 hb (σ : F ≃+* F) hσb
      hσodd').mpr hq
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hcc
      exact hnegb0 hcc.symm
    have hcne : c ≠ -c := by
      intro h
      apply hc0
      have : (2 : F) * c = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left h2
    have hset : ∀ y : F, ((σ : F ≃+* F) y = y ∧ y * y = -b) ↔ y ∈ ({c, -c} : Finset F) := by
      intro y
      rw [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hyy⟩
        have : (y - c) * (y + c) = 0 := by linear_combination hyy - hcc
        rcases mul_eq_zero.mp this with h | h
        · left; linear_combination h
        · right; linear_combination h
      · rintro (rfl | rfl)
        · exact ⟨hc, hcc⟩
        · exact ⟨by rw [map_neg, hc], by rw [neg_mul_neg, hcc]⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hset), Nat.card_eq_fintype_card,
      Fintype.card_coe, Finset.card_pair hcne]
    norm_num
  · rw [Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨y, hy⟩ => hq ((isSquare_neg_fixedField F b
      h2 hb (σ : F ≃+* F) hσb hσodd').mp ⟨y, hy⟩)⟩)]
    norm_num

end CyclicField

section ProjectiveLines

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

open CFSG.GorensteinWalter in
theorem coordinateEquiv_fieldExtension (σ : F ≃+* F) (x : Omega F) (v : Fin 2 → F)
    (hv : v ≠ 0) (hx : coordinateEquiv F x = Projectivization.mk F v hv)
    (hσv : (fun i => σ (v i)) ≠ 0) :
    coordinateEquiv F (fieldExtension F σ x) = Projectivization.mk F (fun i => σ (v i)) hσv := by
  cases x with
  | none =>
    rw [coordinateEquiv_none, psl2ProjectiveInfinity, Projectivization.mk_eq_mk_iff'] at hx
    obtain ⟨a, ha⟩ := hx
    rw [fieldExtension_none, coordinateEquiv_none, psl2ProjectiveInfinity,
      Projectivization.mk_eq_mk_iff']
    have h0 : a * v 0 = 1 := by simpa using congrFun ha 0
    have h1 : a * v 1 = 0 := by simpa using congrFun ha 1
    refine ⟨σ a, ?_⟩
    ext i
    fin_cases i
    · simp [← map_mul, h0]
    · simp [← map_mul, h1]
  | some y =>
    rw [coordinateEquiv_some, psl2AffinePoint, Projectivization.mk_eq_mk_iff'] at hx
    obtain ⟨a, ha⟩ := hx
    rw [fieldExtension_some, coordinateEquiv_some, psl2AffinePoint,
      Projectivization.mk_eq_mk_iff']
    have h0 : a * v 0 = y := by simpa using congrFun ha 0
    have h1 : a * v 1 = 1 := by simpa using congrFun ha 1
    refine ⟨σ a, ?_⟩
    ext i
    fin_cases i
    · simp [← map_mul, h0]
    · simp [← map_mul, h1]

theorem semilinearAction_projective (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m))
    (σ : Sigma) (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0)
    (hwv : w = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
      GeneralLinearGroup (Fin 2) F).val *ᵥ fun i => (σ : F ≃+* F) (v i)) :
    coordinateEquiv F ((⟨quotientClass F b m hm heven X j, σ⟩ :
        SemilinearExtension F b m hm heven Sigma hSigma) •
        (coordinateEquiv F).symm (Projectivization.mk F v hv)) = Projectivization.mk F w hw := by
  set C := SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val with hC
  have hσv : (fun i => (σ : F ≃+* F) (v i)) ≠ 0 := by
    intro h
    apply hv
    funext i
    have := congrFun h i
    simpa using this
  rw [semilinearExtension_smul_def, semilinearAction_mk, projAction_quotientClass,
    Equiv.Perm.mul_apply]
  change coordinateEquiv F (coordinatePGLAction F (Matrix.ProjGenLinGroup.mk C) _) = _
  rw [coordinatePGLAction_point, coordinateEquiv_fieldExtension F (σ : F ≃+* F) _ v hv
    ((coordinateEquiv F).apply_symm_apply _) hσv, Projectivization.PGL.mk_smul_mk]
  congr 1
  rw [hwv, Units.smul_def]
  rfl

end ProjectiveLines

end CFSG.Wreathed.CentralSL2
