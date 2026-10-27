module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cCSL2Conj

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix CFSG CFSG.GH74.GLS.Stage4.Rest

variable {F : Type} [Field F]

theorem m3_isConj_of_not_scalar [Fintype F] [CharP F 2] {g h : SLm F}
    (hg : ∀ c : F, (g : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (hh : ∀ c : F, (h : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (ht : (g : Matrix (Fin 2) (Fin 2) F).trace = (h : Matrix (Fin 2) (Fin 2) F).trace) :
    IsConj g h := by
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
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (x.det)⁻¹
  set y : Matrix (Fin 2) (Fin 2) F := b • x with hy
  have hydet : y.det = 1 := by
    rw [hy, Matrix.det_smul, Fintype.card_fin, pow_two, ← hb]
    exact inv_mul_cancel₀ hxdet
  obtain ⟨c, hc⟩ : ∃ c : SLm F, (c : Matrix (Fin 2) (Fin 2) F) = y := ⟨⟨y, hydet⟩, rfl⟩
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show (c : Matrix (Fin 2) (Fin 2) F) * G = H * (c : Matrix (Fin 2) (Fin 2) F)
  rw [hc, hy, smul_mul_assoc, hxG, mul_smul_comm]

theorem m3_isConj_of_trace_eq [Fintype F] [CharP F 2] {g h : SLm F}
    (hg : IsPRegular 2 g) (hh : IsPRegular 2 h)
    (ht : (g : Matrix (Fin 2) (Fin 2) F).trace = (h : Matrix (Fin 2) (Fin 2) F).trace) :
    IsConj g h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h2' : (-2 : F) = 0 := by rw [h2, neg_zero]
  by_cases h0 : (g : Matrix (Fin 2) (Fin 2) F).trace = 0
  · have e1 := sl2c_eq_one_of_trace_two 2 hg (by rw [h0, h2])
    have e2 := sl2c_eq_one_of_trace_two 2 hh (by rw [← ht, h0, h2])
    have : g = h := Subtype.ext (e1.trans e2.symm)
    rw [this]
  · refine m3_isConj_of_not_scalar ?_ ?_ ht
    · exact sl2c_not_scalar_of_trace_ne _ g.2 (by rwa [h2]) (by rwa [h2'])
    · exact sl2c_not_scalar_of_trace_ne _ h.2 (by rw [← ht, h2]; exact h0)
        (by rw [← ht, h2']; exact h0)

theorem m3_card_twoRegularClass_le [Fintype F] [CharP F 2] :
    Fintype.card (PRegularClass 2 (SLm F)) ≤ Fintype.card F := by
  classical
  refine Fintype.card_le_of_injective
    (fun C => ((PRegularClass.repr C : SLm F) : Matrix (Fin 2) (Fin 2) F).trace) ?_
  intro C C' h
  have hconj := m3_isConj_of_trace_eq (PRegularClass.repr_isPRegular C)
    (PRegularClass.repr_isPRegular C') h
  apply PRegularClass.ext
  have h1 : ConjClasses.mk (PRegularClass.repr C) = C.1 := Quotient.out_eq C.1
  have h2 : ConjClasses.mk (PRegularClass.repr C') = C'.1 := Quotient.out_eq C'.1
  rw [← h1, ← h2]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr hconj

end CFSG.CGT.PushingUpLit.CGT6
