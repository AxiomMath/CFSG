module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def uGlAut (φ : K ≃+* K) (D : uU h n) : uU h n :=
  ⟨glAut φ (D : GL (Fin n) K), glAut_mem_primeFormUnitary h uGram_one φ D.2⟩

theorem coe_uGlAut (φ : K ≃+* K) (D : uU h n) :
    (((uGlAut h φ D : uU h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ := rfl

theorem uFieldAut_mul_uConjAut (hn : 1 ≤ n) (φ : K ≃+* K) (D : uU h n) :
    uFieldAut h hn φ * uConjAut h hn D = uConjAut h hn (uGlAut h φ D) * uFieldAut h hn φ := by
  ext x
  obtain ⟨g, rfl⟩ := projH_surjective x
  rw [MulAut.mul_apply, MulAut.mul_apply, uConjAut_proj, uFieldAut_proj, uFieldAut_proj,
    uConjAut_proj]
  congr 1
  apply Subtype.ext
  change glAut φ ((D : GL (Fin n) K) * (g : GL (Fin n) K) * (D : GL (Fin n) K)⁻¹) =
    glAut φ (D : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (glAut φ (D : GL (Fin n) K))⁻¹
  rw [map_mul, map_mul, map_inv]

theorem exists_scalar_of_commute_graph (hn : 3 ≤ n) {A D : uU h n}
    (hc : uConjAut h (by omega) D * (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) =
      (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) * uConjAut h (by omega) D) :
    ∃ κ : Kˣ, ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (κ : K) • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar) := by
  have e : uConjAut h (by omega) (D * A) =
      uConjAut h (by omega) (A * uGlAut h (barEq h) D) := by
    have := hc
    rw [mul_assoc, uFieldAut_mul_uConjAut, ← mul_assoc, ← mul_assoc, ← map_mul,
      ← map_mul] at this
    exact mul_right_cancel this
  have e1 : uConjAut h (by omega) ((A * uGlAut h (barEq h) D)⁻¹ * (D * A)) = 1 := by
    rw [map_mul, map_inv, e, inv_mul_cancel]
  obtain ⟨c, hc'⟩ := (uConjAut_eq_one_iff h hn _).1 e1
  refine ⟨c, ?_⟩
  have e2 : ((D * A : uU h n) : GL (Fin n) K) =
      ((A * uGlAut h (barEq h) D : uU h n) : GL (Fin n) K) *
        GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hc', ← Subgroup.coe_mul, mul_inv_cancel_left]
  have e3 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) e2
  simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_uGlAut] at e3
  rw [e3, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  rfl

theorem fix_fixedField_of_fix_circle (hp2 : p ≠ 2) {τ : K ≃+* K}
    (hc : ∀ a b : h.fixedField, a ^ 2 + b ^ 2 = 1 → τ (a : K) = a) (c : h.fixedField) :
    τ (c : K) = c := by
  have := h.finite
  have := h.charP
  have h2K : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  have h2 : (2 : h.fixedField) ≠ 0 := fun e => h2K (by
    have h1 : ((1 + 1 : h.fixedField) : K) = 1 + 1 := by rw [Subfield.coe_add, Subfield.coe_one]
    rw [← one_add_one_eq_two] at e ⊢
    rw [← h1, e, Subfield.coe_zero])
  have hF2 : ringChar h.fixedField ≠ 2 := fun e => h2 (by
    have := ringChar.spec h.fixedField 2
    exact_mod_cast (this.2 (by rw [e])))
  have hsq : ∀ t : h.fixedField, τ ((t : K) ^ 2) = (t : K) ^ 2 := by
    intro t
    by_cases ht : 1 + t ^ 2 = 0
    · have : t ^ 2 = -1 := by linear_combination ht
      have e : ((t : K) ^ 2) = -1 := by
        have e' := congrArg Subtype.val this
        push_cast at e'
        exact e'
      rw [e, map_neg, map_one]
    · set a := (1 - t ^ 2) / (1 + t ^ 2) with ha
      have hcirc : a ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
        rw [ha]
        field_simp
        ring
      have hτa := hc a _ hcirc
      have h1a : 1 + a ≠ 0 := by
        rw [ha]
        intro h0
        field_simp at h0
        exact h2 (by linear_combination h0)
      have ht2 : t ^ 2 = (1 - a) / (1 + a) := by
        rw [eq_div_iff h1a, ha]
        field_simp
        ring
      have ht2K : (t : K) ^ 2 = (1 - (a : K)) / (1 + (a : K)) := by
        have e' := congrArg Subtype.val ht2
        push_cast at e'
        exact e'
      rw [ht2K, map_div₀, map_sub, map_add, map_one, hτa]
  obtain ⟨a, b, rfl⟩ := PSL.exists_sq_add_sq hF2 c
  push_cast
  rw [map_add, hsq, hsq]

end CFSG.ComponentClassification.Burgoyne.U
