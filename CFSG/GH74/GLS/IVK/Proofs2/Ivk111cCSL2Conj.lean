module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cCSL2Mat
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PRegularClass

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Matrix Polynomial

section Norm

variable {F : Type} [Field F]

theorem sl2c_exists_norm_eq [Fintype F] (hodd : Fintype.card F % 2 = 1) (h2 : (2 : F) ≠ 0) {t : F}
    (ht : t ^ 2 ≠ 4) (d : F) : ∃ a b : F, a * a + t * a * b + b * b = d := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hc : (4 - t ^ 2 : F) ≠ 0 := fun h => ht (by linear_combination -h)
  obtain ⟨a', b', hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := (X : F[X]) ^ 2) (g := C (4 - t ^ 2) * X ^ 2 - C (4 * d)) (by compute_degree!)
    (by
      rw [sub_eq_add_neg, ← C_neg]
      compute_degree!) hodd
  refine ⟨(a' - t * b') / 2, b', ?_⟩
  simp only [eval_pow, eval_X, eval_sub, eval_mul, eval_C] at hab
  have e1 : (a' - t * b') / 2 * ((a' - t * b') / 2) + t * ((a' - t * b') / 2) * b' + b' * b' =
      (a' ^ 2 + (4 - t ^ 2) * b' ^ 2) / 4 := by
    field_simp
    ring
  have e2 : a' ^ 2 + (4 - t ^ 2) * b' ^ 2 = 4 * d := by linear_combination hab
  rw [e1, e2]
  field_simp

end Norm

section Conj

variable {F : Type} [Field F]

theorem sl2c_det_smul_one_add_smul (H : Matrix (Fin 2) (Fin 2) F) (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • H).det =
      a * a + a * b * H.trace + b * b * H.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul]
  simp
  ring

theorem sl2c_isConj_of_trace_eq_of_not_scalar [Fintype F] (hodd : Fintype.card F % 2 = 1)
    (h2 : (2 : F) ≠ 0) {g h : SLm F}
    (hg : ∀ c : F, (g : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hh : ∀ c : F, (h : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (ht : (g : Matrix (Fin 2) (Fin 2) F).trace = (h : Matrix (Fin 2) (Fin 2) F).trace)
    (ht2 : (g : Matrix (Fin 2) (Fin 2) F).trace ^ 2 ≠ 4) : IsConj g h := by
  obtain ⟨v, hv⟩ := sl2c_exists_cyclic_vector (g : Matrix (Fin 2) (Fin 2) F) hg
  obtain ⟨v', hv'⟩ := sl2c_exists_cyclic_vector (h : Matrix (Fin 2) (Fin 2) F) hh
  set G : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hG
  set H : Matrix (Fin 2) (Fin 2) F := (h : Matrix (Fin 2) (Fin 2) F) with hH
  set P : Matrix (Fin 2) (Fin 2) F := !![v 0, (G *ᵥ v) 0; v 1, (G *ᵥ v) 1] with hP
  set P' : Matrix (Fin 2) (Fin 2) F := !![v' 0, (H *ᵥ v') 0; v' 1, (H *ᵥ v') 1] with hP'
  have hPdet : P.det ≠ 0 := by
    rw [hP, Matrix.det_fin_two_of]
    exact hv
  have hP'det : P'.det ≠ 0 := by
    rw [hP', Matrix.det_fin_two_of]
    exact hv'
  have hPunit : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  have hP'unit : IsUnit P'.det := isUnit_iff_ne_zero.mpr hP'det
  have hGP : G * P = P * !![0, -1; 1, G.trace] := sl2c_mul_companion G g.2 v
  have hHP : H * P' = P' * !![0, -1; 1, G.trace] := by
    rw [ht]
    exact sl2c_mul_companion H h.2 v'
  set C : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, G.trace] with hC
  have hinvG : P⁻¹ * G = C * P⁻¹ := by
    calc P⁻¹ * G = P⁻¹ * G * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv P hPunit, Matrix.mul_one]
      _ = P⁻¹ * (G * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (P * C) * P⁻¹ := by rw [hGP]
      _ = C * P⁻¹ := by
        rw [← Matrix.mul_assoc P⁻¹ P C, Matrix.nonsing_inv_mul P hPunit, Matrix.one_mul]
  set x : Matrix (Fin 2) (Fin 2) F := P' * P⁻¹ with hx
  have hxG : x * G = H * x := by
    rw [hx, Matrix.mul_assoc, hinvG, ← Matrix.mul_assoc, ← hHP, Matrix.mul_assoc]
  have hxdet : x.det ≠ 0 := by
    rw [hx, Matrix.det_mul]
    refine mul_ne_zero hP'det ?_
    intro h0
    have := Matrix.det_nonsing_inv_mul_det P hPunit
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  obtain ⟨a, b, hab⟩ := sl2c_exists_norm_eq hodd h2 ht2 (x.det)⁻¹
  set z : Matrix (Fin 2) (Fin 2) F := a • (1 : Matrix (Fin 2) (Fin 2) F) + b • H with hz
  have hzH : z * H = H * z := by
    rw [hz]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  have hzdet : z.det = (x.det)⁻¹ := by
    rw [hz, sl2c_det_smul_one_add_smul, h.2, ← hab, ← ht]
    ring
  set y : Matrix (Fin 2) (Fin 2) F := z * x with hy
  have hydet : y.det = 1 := by
    rw [hy, Matrix.det_mul, hzdet]
    exact inv_mul_cancel₀ hxdet
  obtain ⟨c, hc⟩ : ∃ c : SLm F, (c : Matrix (Fin 2) (Fin 2) F) = y := ⟨⟨y, hydet⟩, rfl⟩
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show (c : Matrix (Fin 2) (Fin 2) F) * G = H * (c : Matrix (Fin 2) (Fin 2) F)
  rw [hc, hy, Matrix.mul_assoc, hxG, ← Matrix.mul_assoc, hzH, Matrix.mul_assoc]

end Conj

section Regular

open CFSG

variable {F : Type} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

theorem sl2c_natCast_ne_zero_of_coprime {m : ℕ} (hm : Nat.Coprime m p) : (m : F) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff F p] at h
  exact (Fact.out : p.Prime).one_lt.ne' (hm.symm.eq_one_of_dvd h)

theorem sl2c_two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

theorem sl2c_eq_one_of_trace_two {g : SLm F} (hg : IsPRegular p g)
    (ht : (g : Matrix (Fin 2) (Fin 2) F).trace = 2) : (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have hm : (orderOf g : F) ≠ 0 := sl2c_natCast_ne_zero_of_coprime p hg
  refine sl2c_eq_one_of_sq_eq ?_ hm ?_
  · rw [sl2c_cayley_hamilton, ht, g.2, one_smul]
  · rw [← Matrix.SpecialLinearGroup.coe_pow, pow_orderOf_eq_one]
    rfl

theorem sl2c_eq_neg_one_of_trace_neg_two (hp2 : p ≠ 2) {g : SLm F} (hg : IsPRegular p g)
    (ht : (g : Matrix (Fin 2) (Fin 2) F).trace = -2) :
    (g : Matrix (Fin 2) (Fin 2) F) = -1 := by
  have hm : (orderOf g : F) ≠ 0 := sl2c_natCast_ne_zero_of_coprime p hg
  have hm2 : ((2 * orderOf g : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    exact mul_ne_zero (sl2c_two_ne_zero_of_ne_two p hp2) hm
  have key : -(g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    refine sl2c_eq_one_of_sq_eq (m := 2 * orderOf g) ?_ hm2 ?_
    · rw [neg_mul_neg, sl2c_cayley_hamilton, ht, g.2, one_smul, smul_neg, neg_smul]
    · rw [Even.neg_pow (even_two_mul _), ← Matrix.SpecialLinearGroup.coe_pow, pow_mul',
        pow_orderOf_eq_one, one_pow]
      rfl
  rw [neg_eq_iff_eq_neg] at key
  exact key

theorem sl2c_not_scalar_of_trace_ne (G : Matrix (Fin 2) (Fin 2) F) (hdet : G.det = 1)
    (h1 : G.trace ≠ 2) (h2 : G.trace ≠ -2) : ∀ c : F, G ≠ c • 1 := by
  intro c hc
  rw [hc] at hdet h1 h2
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul] at hdet h1 h2
  simp at hdet h1 h2
  have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp hc2 with h | h
  · exact h1 (by linear_combination (2 : F) * h)
  · exact h2 (by linear_combination (2 : F) * h)

theorem sl2c_isConj_of_trace_eq [Fintype F] (hp2 : p ≠ 2) (hodd : Fintype.card F % 2 = 1) {g h : SLm F}
    (hg : IsPRegular p g) (hh : IsPRegular p h)
    (ht : (g : Matrix (Fin 2) (Fin 2) F).trace = (h : Matrix (Fin 2) (Fin 2) F).trace) :
    IsConj g h := by
  have h2 : (2 : F) ≠ 0 := sl2c_two_ne_zero_of_ne_two p hp2
  by_cases h1 : (g : Matrix (Fin 2) (Fin 2) F).trace = 2
  · have e1 := sl2c_eq_one_of_trace_two p hg h1
    have e2 := sl2c_eq_one_of_trace_two p hh (ht ▸ h1)
    have : g = h := Subtype.ext (e1.trans e2.symm)
    rw [this]
  by_cases h1' : (g : Matrix (Fin 2) (Fin 2) F).trace = -2
  · have e1 := sl2c_eq_neg_one_of_trace_neg_two p hp2 hg h1'
    have e2 := sl2c_eq_neg_one_of_trace_neg_two p hp2 hh (ht ▸ h1')
    have : g = h := Subtype.ext (e1.trans e2.symm)
    rw [this]
  refine sl2c_isConj_of_trace_eq_of_not_scalar hodd h2 ?_ ?_ ht ?_
  · exact sl2c_not_scalar_of_trace_ne _ g.2 h1 h1'
  · exact sl2c_not_scalar_of_trace_ne _ h.2 (ht ▸ h1) (ht ▸ h1')
  · intro hsq
    have : ((g : Matrix (Fin 2) (Fin 2) F).trace - 2) * ((g : Matrix (Fin 2) (Fin 2) F).trace + 2) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact h1 (by linear_combination h)
    · exact h1' (by linear_combination h)

theorem sl2c_card_pRegularClass_le [Fintype F] (hp2 : p ≠ 2) (hodd : Fintype.card F % 2 = 1) :
    Fintype.card (PRegularClass p (SLm F)) ≤ Fintype.card F := by
  classical
  refine Fintype.card_le_of_injective
    (fun C => ((PRegularClass.repr C : SLm F) : Matrix (Fin 2) (Fin 2) F).trace) ?_
  intro C C' h
  have hconj := sl2c_isConj_of_trace_eq p hp2 hodd (PRegularClass.repr_isPRegular C)
    (PRegularClass.repr_isPRegular C') h
  apply PRegularClass.ext
  have h1 : ConjClasses.mk (PRegularClass.repr C) = C.1 := Quotient.out_eq C.1
  have h2 : ConjClasses.mk (PRegularClass.repr C') = C'.1 := Quotient.out_eq C'.1
  rw [← h1, ← h2]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr hconj

end Regular

end CFSG.GH74.GLS.Stage4.Rest
