module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix

section NormOne

variable (F : Type) (E : Type) [Field E]

@[expose] noncomputable def normOne : Subgroup Eˣ := rootsOfUnity (Nat.card F + 1) E

theorem mem_normOne_iff (t : Eˣ) :
    t ∈ normOne F E ↔ (t : E) * (t : E) ^ Nat.card F = 1 := by
  rw [normOne, mem_rootsOfUnity, ← Units.val_eq_one, Units.val_pow_eq_pow_val, pow_succ']

instance normOne_isCyclic : IsCyclic (normOne F E) := by
  unfold normOne
  infer_instance

theorem pow_card_of_mem_normOne {t : Eˣ} (ht : t ∈ normOne F E) :
    (t : E) ^ Nat.card F = (t : E)⁻¹ := by
  rw [mem_normOne_iff] at ht
  exact eq_inv_of_mul_eq_one_right ht

end NormOne

section Matrices

variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
  (basis : Module.Basis (Fin 2) F E)

include basis in
theorem finrank_eq_two : Module.finrank F E = 2 := by
  rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]

noncomputable abbrev mulMatrix (t : E) : Matrix (Fin 2) (Fin 2) F := Algebra.leftMulMatrix basis t

theorem mulMatrix_algebraMap (c : F) :
    mulMatrix F E basis (algebraMap F E c) = Matrix.scalar (Fin 2) c := by
  rw [mulMatrix, AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
  rfl

theorem mulMatrix_injective : Function.Injective (mulMatrix F E basis) :=
  Algebra.leftMulMatrix_injective basis

@[expose] noncomputable def mulGL : Eˣ →* GL (Fin 2) F :=
  Units.map (Algebra.leftMulMatrix basis).toMonoidHom

theorem mulGL_val (t : Eˣ) :
    ((mulGL F E basis t : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = mulMatrix F E basis t := rfl

include basis in
theorem card_extension : Nat.card E = Nat.card F ^ 2 := by
  have : Module.Finite F E := Module.Finite.of_basis basis
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_eq_two F E basis]

end Matrices

section Extension

variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Algebra F E]
  (basis : Module.Basis (Fin 2) F E)

include basis in
theorem finite_of_basis : Finite E := by
  have : Module.Finite F E := Module.Finite.of_basis basis
  exact Module.finite_of_finite F

theorem two_le_card : 2 ≤ Nat.card F := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

theorem card_sq_sub_one : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
  have h := two_le_card F
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = k + 1 := ⟨Nat.card F - 1, by omega⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

include basis in
theorem algebraMap_norm (t : E) :
    algebraMap F E (Algebra.norm F t) = t * t ^ Nat.card F := by
  have := finite_of_basis F E basis
  rw [FiniteField.algebraMap_norm_eq_pow, card_extension F E basis, card_sq_sub_one,
    Nat.mul_div_cancel_left _ (by have := two_le_card F; omega), pow_succ']

theorem pow_card_algebraMap (c : F) :
    (algebraMap F E c) ^ Nat.card F = algebraMap F E c := by
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

include basis in
theorem pow_card_pow_card (t : E) : (t ^ Nat.card F) ^ Nat.card F = t := by
  have := finite_of_basis F E basis
  have : Fintype E := Fintype.ofFinite E
  rw [← pow_mul, ← sq, ← card_extension F E basis, Nat.card_eq_fintype_card, FiniteField.pow_card]

include basis in
theorem exists_generator_normOne :
    ∃ γ : Eˣ, (∀ s : Eˣ, s ∈ Subgroup.zpowers γ) ∧
      orderOf γ = (Nat.card F - 1) * (Nat.card F + 1) ∧
      orderOf (γ ^ (Nat.card F - 1)) = Nat.card F + 1 ∧ γ ^ (Nat.card F - 1) ∈ normOne F E := by
  have := finite_of_basis F E basis
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord : orderOf γ = (Nat.card F - 1) * (Nat.card F + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, card_extension F E basis,
      card_sq_sub_one]
  have hq := two_le_card F
  have hord' : orderOf (γ ^ (Nat.card F - 1)) = Nat.card F + 1 := by
    rw [orderOf_pow_of_dvd (by omega) ⟨Nat.card F + 1, hord⟩, hord,
      Nat.mul_div_cancel_left _ (by omega)]
  refine ⟨γ, hγ, hord, hord', ?_⟩
  rw [normOne, mem_rootsOfUnity, ← hord']
  exact pow_orderOf_eq_one _

include basis in
theorem card_normOne : Nat.card (normOne F E) = Nat.card F + 1 := by
  obtain ⟨γ, -, -, hord, -⟩ := exists_generator_normOne F E basis
  have hprim : IsPrimitiveRoot ((γ ^ (Nat.card F - 1) : Eˣ) : E) (Nat.card F + 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hord]
    exact IsPrimitiveRoot.orderOf _
  exact hprim.card_rootsOfUnity

theorem algebraMap_det_mulMatrix (t : E) :
    algebraMap F E (mulMatrix F E basis t).det = t * t ^ Nat.card F := by
  rw [← Algebra.norm_eq_matrix_det, algebraMap_norm F E basis]

theorem det_mulMatrix_eq_one {t : Eˣ} (ht : t ∈ normOne F E) :
    (mulMatrix F E basis (t : E)).det = 1 := by
  apply (algebraMap F E).injective
  rw [algebraMap_det_mulMatrix, map_one]
  exact (mem_normOne_iff F E t).mp ht

@[expose] noncomputable def mulSL : normOne F E →* SpecialLinearGroup (Fin 2) F where
  toFun t := ⟨mulMatrix F E basis ((t : Eˣ) : E), det_mulMatrix_eq_one F E basis t.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    change mulMatrix F E basis (((s * t : normOne F E) : Eˣ) : E) =
      mulMatrix F E basis ((s : Eˣ) : E) * mulMatrix F E basis ((t : Eˣ) : E)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact map_mul (Algebra.leftMulMatrix basis) _ _)

theorem mulSL_val (t : normOne F E) :
    ((mulSL F E basis t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      mulMatrix F E basis ((t : Eˣ) : E) := rfl

theorem mulSL_injective : Function.Injective (mulSL F E basis) := by
  intro s t h
  have h' := congrArg (fun X : SpecialLinearGroup (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) h
  simp only [mulSL_val] at h'
  exact Subtype.ext (Units.ext (mulMatrix_injective F E basis h'))

@[expose] noncomputable def frobMatrix : Matrix (Fin 2) (Fin 2) F :=
  LinearMap.toMatrix basis basis (FiniteField.frobeniusAlgHom F E).toLinearMap

theorem frobeniusAlgHom_apply' (t : E) :
    FiniteField.frobeniusAlgHom F E t = t ^ Nat.card F := by
  rw [FiniteField.frobeniusAlgHom_apply, Nat.card_eq_fintype_card]

theorem frobMatrix_mul_self : frobMatrix F E basis * frobMatrix F E basis = 1 := by
  rw [frobMatrix, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one basis]
  congr 1
  ext t
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, frobeniusAlgHom_apply',
    Module.End.one_apply]
  exact pow_card_pow_card F E basis t

theorem frobMatrix_mul_mulMatrix (t : E) :
    frobMatrix F E basis * mulMatrix F E basis t =
      mulMatrix F E basis (t ^ Nat.card F) * frobMatrix F E basis := by
  rw [frobMatrix, mulMatrix, mulMatrix, Algebra.leftMulMatrix_apply,
    Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  ext s
  simp only [Module.End.mul_apply, AlgHom.toLinearMap_apply, frobeniusAlgHom_apply',
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_pow]

omit [Fintype F] in
theorem det_eq_neg_one_of_mul_self {A : Matrix (Fin 2) (Fin 2) F} (hA : A * A = 1)
    (h1 : A ≠ 1) (h2 : A ≠ -1) : A.det = -1 := by
  have hCH : A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hA] at hCH
  by_cases ht : A.trace = 0
  · rw [ht, zero_smul, zero_sub] at hCH
    have h00 := congrFun (congrFun hCH 0) 0
    simp only [one_apply_eq, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, mul_one] at h00
    linear_combination h00
  · exfalso
    have htA : A.trace • A = (1 + A.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [add_smul, one_smul]
      exact (eq_sub_iff_add_eq.mp hCH).symm
    have hA' : A = (A.trace⁻¹ * (1 + A.det)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [mul_smul, ← htA, smul_smul, inv_mul_cancel₀ ht, one_smul]
    set c := A.trace⁻¹ * (1 + A.det)
    have hc : c * c = 1 := by
      have h := hA
      rw [hA', smul_mul_smul, one_mul] at h
      have h00 := congrFun (congrFun h 0) 0
      simpa using h00
    rcases mul_self_eq_one_iff.mp hc with h | h
    · exact h1 (by rw [hA', h, one_smul])
    · exact h2 (by rw [hA', h, neg_one_smul])

theorem det_frobMatrix (h2 : (2 : F) ≠ 0) : (frobMatrix F E basis).det = -1 := by
  have := finite_of_basis F E basis
  apply det_eq_neg_one_of_mul_self F (frobMatrix_mul_self F E basis)
  · intro h
    have hσ : (FiniteField.frobeniusAlgHom F E).toLinearMap = LinearMap.id := by
      apply (LinearMap.toMatrix basis basis).injective
      rw [LinearMap.toMatrix_id]
      exact h
    have h1 : FiniteField.frobeniusAlgHom F E = 1 := by
      ext t
      exact LinearMap.congr_fun hσ t
    have hord := FiniteField.orderOf_frobeniusAlgHom F E
    rw [h1, orderOf_one, finrank_eq_two F E basis] at hord
    exact absurd hord (by norm_num)
  · intro h
    have hσ : (FiniteField.frobeniusAlgHom F E).toLinearMap = -LinearMap.id := by
      apply (LinearMap.toMatrix basis basis).injective
      rw [map_neg, LinearMap.toMatrix_id]
      exact h
    have h1 := LinearMap.congr_fun hσ 1
    simp only [AlgHom.toLinearMap_apply, map_one, LinearMap.neg_apply, LinearMap.id_apply] at h1
    apply h2
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]
    linear_combination h1

include basis in
theorem exists_norm_eq (c : Fˣ) : ∃ z : Eˣ, (z : E) * (z : E) ^ Nat.card F = algebraMap F E c := by
  have := finite_of_basis F E basis
  obtain ⟨z, hz⟩ := FiniteField.unitsMap_norm_surjective F E c
  refine ⟨z, ?_⟩
  rw [← algebraMap_norm F E basis]
  congr 1
  exact congrArg Units.val hz

end Extension

section Constants

variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Algebra F E]
  (basis : Module.Basis (Fin 2) F E) (b : Fˣ) (m : ℕ)

abbrev unitE : Eˣ := Units.map (algebraMap F E).toMonoidHom b

omit [Fintype F] in
theorem unitE_val : ((unitE F E b : Eˣ) : E) = algebraMap F E b := rfl

theorem odd_card (h2 : (2 : F) ≠ 0) : Odd (Nat.card F) := by
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  refine FiniteField.odd_card_of_char_ne_two fun hc => h2 ?_
  exact_mod_cast (ringChar.spec F 2).mpr (by rw [hc])

omit [Algebra F E] in
theorem neg_one_mem_normOne (h2 : (2 : F) ≠ 0) : (-1 : Eˣ) ∈ normOne F E := by
  rw [mem_normOne_iff, Units.val_neg, Units.val_one, (odd_card F h2).neg_one_pow]
  ring

@[expose] noncomputable def negOneE (h2 : (2 : F) ≠ 0) : normOne F E :=
  ⟨-1, neg_one_mem_normOne F E h2⟩

variable {F E b} in
theorem r_mem_normOne (h2 : (2 : F) ≠ 0) {z : Eˣ}
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    -(z ^ 2) * (unitE F E b)⁻¹ ∈ normOne F E := by
  rw [mem_normOne_iff]
  have hB : (algebraMap F E b) ≠ 0 := by simp
  simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    unitE_val]
  rw [mul_pow, neg_pow, (odd_card F h2).neg_one_pow, inv_pow, pow_card_algebraMap, ← pow_mul,
    mul_comm 2, pow_mul]
  have key : (z : E) ^ 2 * ((z : E) ^ Nat.card F) ^ 2 = (algebraMap F E b) ^ 2 := by
    rw [← mul_pow, hz]
  field_simp
  linear_combination key

@[expose] noncomputable def rE (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) : normOne F E :=
  ⟨-(z ^ 2) * (unitE F E b)⁻¹, r_mem_normOne h2 hz⟩

theorem rE_val (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    (((rE F E b h2 z hz : normOne F E) : Eˣ) : E) = -((z : E) ^ 2) / algebraMap F E b := by
  simp [rE, div_eq_mul_inv]

include basis in
theorem β_mem_normOne (z : Eˣ) : z ^ Nat.card F * z⁻¹ ∈ normOne F E := by
  rw [mem_normOne_iff]
  have hz0 : (z : E) ≠ 0 := z.ne_zero
  have hzq : (z : E) ^ Nat.card F ≠ 0 := pow_ne_zero _ hz0
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rw [mul_pow, inv_pow, pow_card_pow_card F E basis]
  field_simp

include basis in
@[expose] noncomputable def βE (z : Eˣ) : normOne F E :=
  ⟨z ^ Nat.card F * z⁻¹, β_mem_normOne F E basis z⟩

theorem βE_val (z : Eˣ) :
    (((βE F E basis z : normOne F E) : Eˣ) : E) = (z : E) ^ Nat.card F / z := by
  simp [βE, div_eq_mul_inv]

@[expose] noncomputable def cMinus (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) : normOne F E :=
  negOneE F E h2 * rE F E b h2 z hz ^ (m / 2)

theorem βE_eq (h2 : (2 : F) ≠ 0) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    βE F E basis z = negOneE F E h2 * (rE F E b h2 z hz)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, Units.val_inv_eq_inv_val, rE_val,
    βE_val]
  have hz0 : (z : E) ≠ 0 := z.ne_zero
  have hB : (algebraMap F E b) ≠ 0 := by simp
  have hz' : (z : E) ^ Nat.card F = algebraMap F E b / (z : E) := by
    rw [← hz]
    field_simp
  rw [hz']
  simp only [negOneE, Units.val_neg, Units.val_one]
  field_simp

theorem βE_not_isSquare (h2 : (2 : F) ≠ 0) (hb : ¬ IsSquare b) (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    ¬ IsSquare (βE F E basis z) := by
  obtain ⟨γ, hγ, -, hord, hmem⟩ := exists_generator_normOne F E basis
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hγ z)
  have hq := two_le_card F
  have : Finite E := finite_of_basis F E basis
  have hzU : z ^ (Nat.card F + 1) = unitE F E b := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ', hz]
    rfl
  have hγN : γ ^ (Nat.card F + 1) =
      unitE F E (Units.map (Algebra.norm F) γ) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_succ', unitE_val, Units.coe_map,
      algebraMap_norm F E basis]
  have hbk : b = (Units.map (Algebra.norm F) γ) ^ k := by
    apply Units.map_injective (f := (algebraMap F E).toMonoidHom) (algebraMap F E).injective
    rw [map_zpow]
    change unitE F E b = unitE F E (Units.map (Algebra.norm F) γ) ^ k
    rw [← hγN, ← hzU, ← hk, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
      ← _root_.zpow_mul, mul_comm]
  have hkodd : Odd k := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨j, hj⟩ := hev
    exact hb ⟨_ ^ j, by rw [hbk, hj, _root_.zpow_add]⟩
  have hE1 : Subgroup.zpowers (γ ^ (Nat.card F - 1)) = normOne F E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact hmem
    · rw [Nat.card_zpowers, hord, card_normOne F E basis]
  have hβ : ((βE F E basis z : normOne F E) : Eˣ) = (γ ^ (Nat.card F - 1)) ^ k := by
    change z ^ Nat.card F * z⁻¹ = _
    rw [← hk, ← zpow_natCast (γ ^ k), ← zpow_natCast γ, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_neg, ← _root_.zpow_add]
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.card F)]
    ring
  rintro ⟨s, hs⟩
  have hs' : (s : Eˣ) ∈ Subgroup.zpowers (γ ^ (Nat.card F - 1)) := by
    rw [hE1]
    exact s.2
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hs'
  have h1 : (γ ^ (Nat.card F - 1)) ^ (k - 2 * i) = 1 := by
    have h3 := congrArg (fun t : normOne F E => (t : Eˣ)) hs
    simp only [Subgroup.coe_mul] at h3
    rw [hβ, ← hi, ← _root_.zpow_add, ← two_mul] at h3
    rw [_root_.zpow_sub, h3, mul_inv_cancel]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hord] at hdvd
  have h2q : (2 : ℤ) ∣ ((Nat.card F + 1 : ℕ) : ℤ) := by
    obtain ⟨j, hj⟩ := odd_card F h2
    exact ⟨j + 1, by push_cast [hj]; ring⟩
  obtain ⟨d, hd⟩ := dvd_trans h2q hdvd
  exact (Int.not_even_iff_odd.mpr hkodd) ⟨d + i, by linarith⟩

end Constants

end CFSG.Wreathed.CentralSL2
