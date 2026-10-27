module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aInvol
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Sub
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Rank

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7

section SL2

variable {F : Type*} [Field F]

@[expose] def up2 (c : F) : SL(2, F) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lo2 (c : F) : SL(2, F) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def dg2 (a : Fˣ) : SL(2, F) :=
  ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

@[expose] def w2 (F : Type*) [Field F] [CharP F 2] : SL(2, F) :=
  ⟨!![0, 1; 1, 0], by
    simp [Matrix.det_fin_two]
    exact neg_eq_iff_add_eq_zero.mpr (by simpa using CharTwo.add_self_eq_zero (1 : F))⟩

theorem up2_zero : up2 (0 : F) = 1 := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;> simp [up2]

theorem dg2_mul (a b : Fˣ) : dg2 a * dg2 b = dg2 (a * b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dg2_one : dg2 (1 : Fˣ) = (1 : SL(2, F)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

theorem dg2_pow (a : Fˣ) (n : ℕ) : (dg2 a) ^ n = dg2 (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, dg2_one]
  | succ n ih => rw [pow_succ, ih, dg2_mul, pow_succ]

theorem dg2_mul_up2 (a : Fˣ) (c : F) : dg2 a * up2 c = up2 ((a : F) ^ 2 * c) * dg2 a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  fin_cases i <;> fin_cases j <;>
    simp [dg2, up2, Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
  field_simp

theorem dg2_conj_up2 (a : Fˣ) (c : F) :
    dg2 a * up2 c * (dg2 a)⁻¹ = up2 ((a : F) ^ 2 * c) := by
  rw [dg2_mul_up2, mul_assoc, mul_inv_cancel, mul_one]

theorem dg2_ne_one {a : Fˣ} (ha : a ≠ 1) : dg2 a ≠ (1 : SL(2, F)) := by
  intro h
  apply ha
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simpa [dg2] using this

theorem w2_mul_self [CharP F 2] : w2 F * w2 F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2, Matrix.mul_apply, Fin.sum_univ_two]

theorem w2_conj_up2 [CharP F 2] (c : F) : w2 F * up2 c * w2 F = lo2 c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2, up2, lo2, Matrix.mul_apply, Fin.sum_univ_two]

end SL2

section Embedding

variable {F : Type*} [Field F]

@[expose] def emb2Mat (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, 1]

theorem emb2Mat_mul (g h : Matrix (Fin 2) (Fin 2) F) :
    emb2Mat (g * h) = emb2Mat g * emb2Mat h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb2Mat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem emb2Mat_one : emb2Mat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb2Mat]

theorem det_emb2Mat (g : Matrix (Fin 2) (Fin 2) F) : (emb2Mat g).det = g.det := by
  simp [emb2Mat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def emb2 : SL(2, F) →* SL(3, F) where
  toFun g := ⟨emb2Mat g, by rw [det_emb2Mat, g.2]⟩
  map_one' := Subtype.ext emb2Mat_one
  map_mul' g h := Subtype.ext (by
    show emb2Mat ((g * h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = emb2Mat g * emb2Mat h
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact emb2Mat_mul (g : Matrix (Fin 2) (Fin 2) F) (h : Matrix (Fin 2) (Fin 2) F))

theorem emb2_coe (g : SL(2, F)) :
    ((emb2 g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = emb2Mat g := rfl

theorem emb2_up2 (c : F) : emb2 (up2 c) = up3 0 0 c := by
  apply Subtype.ext
  show emb2Mat ((up2 c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = upMat 0 0 c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb2Mat, up2, upMat]

theorem eq_one_of_emb2_scalar {g : SL(2, F)} {a : F}
    (h : ((emb2 g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) a) : g = 1 := by
  have h22 := congrFun (congrFun h 2) 2
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp [emb2_coe, emb2Mat] at h22 h00 h11 h01 h10
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10, ← h22]

end Embedding

section Main

variable {F : Type*} [Field F] [CharP F 2] [Fintype F]

omit [CharP F 2] in
theorem odd_orderOf_dg2 {f : ℕ} (hf : 1 ≤ f) (hF : Fintype.card F = 2 ^ f) (a : Fˣ) :
    Odd (orderOf (dg2 a)) := by
  classical
  have hodd : Odd (Fintype.card Fˣ) := by
    rw [Fintype.card_units, hF]
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rw [Nat.odd_iff]
    omega
  refine Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one ?_)
  rw [dg2_pow, pow_card_eq_one, dg2_one]

theorem trivial_of_up2_one {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) SL(2, F) Y) (h : σ (up2 1) = 1) : ∀ g, σ g = 1 := by
  have hup : ∀ c : F, σ (up2 c) = 1 := by
    intro c
    by_cases hc : c = 0
    · rw [hc, up2_zero, map_one]
    · obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
      have hs0 : s ≠ 0 := by
        rintro rfl
        apply hc
        rw [hs]
        ring
      have h1 : up2 c = dg2 (Units.mk0 s hs0) * up2 1 * (dg2 (Units.mk0 s hs0))⁻¹ := by
        rw [dg2_conj_up2]
        congr 1
        simp [hs, sq]
      rw [h1, map_mul, map_mul, h, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hlo : ∀ c : F, σ (lo2 c) = 1 := by
    intro c
    rw [← w2_conj_up2, map_mul, map_mul, hup, mul_one, ← map_mul, w2_mul_self, map_one]
  intro g
  have hg : g ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 F) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, j, hij, c, rfl⟩ := hx
    revert hij
    fin_cases i <;> fin_cases j <;> intro hij
    · exact absurd rfl hij
    · have : Matrix.SpecialLinearGroup.transvection hij c = up2 c := by
        apply Subtype.ext
        ext p q
        fin_cases p <;> fin_cases q <;>
          simp [CFSG.LinearGroups.coe_transvection, up2]
      rw [this]
      exact hup c
    · have : Matrix.SpecialLinearGroup.transvection hij c = lo2 c := by
        apply Subtype.ext
        ext p q
        fin_cases p <;> fin_cases q <;>
          simp [CFSG.LinearGroups.coe_transvection, lo2]
      rw [this]
      exact hlo c
    · exact absurd rfl hij
  | one => exact map_one σ
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, mul_one]
  | inv x _ hx =>
    calc σ x⁻¹ = σ x⁻¹ * σ x := by rw [hx, mul_one]
      _ = σ (x⁻¹ * x) := (map_mul σ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, map_one]

omit [Fintype F] in
theorem up2_one_sq : up2 (1 : F) * up2 1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [up2, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

omit [CharP F 2] [Fintype F] in
theorem up2_one_ne_one : up2 (1 : F) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [up2] at this

theorem standard_transvection_rank_ge_two {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ g : SL(3, F), ρ g = 1 →
      ∃ a : F, (g : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) a) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (up3 0 0 1) - 1)) := by
  classical
  by_contra hlt
  push Not at hlt
  set ρK : Representation (ZMod 2) SL(2, F) U := ρ.comp emb2 with hρKdef
  have hρK : ∀ g : SL(2, F), ρK g = 1 → g = 1 := fun g hg => by
    obtain ⟨a, ha⟩ := hker (emb2 g) hg
    exact eq_one_of_emb2_scalar ha
  have hnt : Nontrivial Fˣ := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_units, hF]
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have hodd := odd_orderOf_dg2 (by omega) hF a
  have hρKa : ρK (dg2 a) ≠ 1 := fun h => dg2_ne_one ha (hρK _ h)
  obtain ⟨Y, i1, i2, i3, σ, hirr, hσa, hrank⟩ :=
    exists_irreducible_subquotient (Module.finrank (ZMod 2) U) ρK (dg2 a) rfl hodd hρKa
  have hσt : σ (up2 1) ≠ 1 := fun h => hσa (trivial_of_up2_one σ h (dg2 a))
  have hr1 : Module.finrank (ZMod 2) (LinearMap.range (σ (up2 1) - 1)) ≤ 1 := by
    have h1 := hrank (up2 1)
    have h2 : ρK (up2 1) = ρ (up3 0 0 1) := by
      rw [hρKdef, MonoidHom.comp_apply, emb2_up2]
    rw [h2] at h1
    omega
  have hsq : up2 (1 : F) * up2 1 = 1 := up2_one_sq
  have hinv : (up2 (1 : F))⁻¹ = up2 1 := inv_eq_of_mul_eq_one_right hsq
  let A : Subgroup SL(2, F) := Subgroup.zpowers (up2 (1 : F))
  have hAcard : Nat.card A = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) up2_one_ne_one
  have hAsq : ∀ x : A, x * x = 1 := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hsq, one_zpow]
  have : CFSG.IsElementaryAbelian 2 A := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => ?_)
    rw [pow_two]
    exact hAsq x
  have hA1 : A ≠ ⊥ := by
    intro h
    have : up2 (1 : F) ∈ A := Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at this
    exact up2_one_ne_one this
  have hfix : ∀ y : Y, (∀ x ∈ A, σ x y = y) ↔ y ∈ LinearMap.ker (σ (up2 1) - 1) := by
    intro y
    constructor
    · intro h
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact h _ (Subgroup.mem_zpowers _)
    · intro h x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      clear hx
      induction n using Int.induction_on with
      | zero => simp
      | succ m ihm =>
        rw [zpow_add_one, map_mul]
        show σ (up2 1 ^ (m : ℤ)) (σ (up2 1) y) = y
        rw [h]
        exact ihm
      | pred m ihm =>
        rw [zpow_sub_one, hinv, map_mul]
        show σ (up2 1 ^ (-(m : ℤ))) (σ (up2 1) y) = y
        rw [h]
        exact ihm
  have hoff : Nat.card Y ≤ Nat.card A * Nat.card {y : Y // ∀ x ∈ A, σ x y = y} := by
    have hcard : Nat.card {y : Y // ∀ x ∈ A, σ x y = y} =
        Nat.card (LinearMap.ker (σ (up2 1) - 1)) :=
      Nat.card_congr (Equiv.subtypeEquivRight hfix)
    have hfin : Module.Finite (ZMod 2) Y := Module.Finite.of_finite
    have h1 := LinearMap.finrank_range_add_finrank_ker (σ (up2 1) - 1)
    rw [hcard, hAcard, natCard_eq_two_pow_finrank Y, natCard_eq_two_pow_finrank (LinearMap.ker _),
      ← h1, pow_add]
    exact Nat.mul_le_mul_right _ (by
      calc 2 ^ Module.finrank (ZMod 2) (LinearMap.range (σ (up2 1) - 1)) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) hr1
        _ = 2 := by norm_num)
  obtain ⟨φ, -, -, -, -, ℓ, -, -, -, hcardA', -, -⟩ :=
    CFSG.QuasithinUnique.Setup.SL2Modules.binary_SL2_internal_offender_natural_module (n := f) (by omega) hF σ hirr
      ⟨dg2 a, hσa⟩ A hA1 hoff
  rw [hAcard] at hcardA'
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem involution_rank_ge_two {f : ℕ} (hf : 2 ≤ f) (hF : Fintype.card F = 2 ^ f)
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ g : SL(3, F), ρ g = 1 →
      ∃ a : F, (g : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) a)
    (t : SL(3, F)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  obtain ⟨g, hg⟩ := exists_conj_transvection t ht1 ht2
  have ht : t = g * up3 0 0 1 * g⁻¹ := by rw [← hg]; group
  set ρ' : Representation (ZMod 2) SL(3, F) U := ρ.comp (MulAut.conj g).toMonoidHom with hρ'
  have hρ't : ρ' (up3 0 0 1) = ρ t := by
    rw [ht]
    rfl
  have hker' : ∀ h : SL(3, F), ρ' h = 1 →
      ∃ a : F, (h : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) a := by
    intro h hh
    obtain ⟨a, ha⟩ := hker (g * h * g⁻¹) hh
    refine ⟨a, ?_⟩
    have h1 : h = g⁻¹ * (g * h * g⁻¹) * g := by group
    have hs : (Matrix.scalar (Fin 3) a : Matrix (Fin 3) (Fin 3) F) =
        a • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    have hgg : ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [h1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ha, hs,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hgg]
  rw [← hρ't]
  exact standard_transvection_rank_ge_two hf hF ρ' hker'

end Main

end CFSG.QuasithinUnique.Setup.X7a
