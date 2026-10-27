module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearPerfect
public import CFSG.LieType.SeitzGeneration.OuterLinearLift
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Curtis.Coordinator (autFix)

variable {n : ℕ} {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem conjAut_inner_of_det_eq_one {A : GL (Fin n) F}
    (hd : (A : Matrix (Fin n) (Fin n) F).det = 1) :
    ∃ k : projectiveSL n F, conjAut n F A = MulAut.conj k := by
  let X : SpecialLinearGroup (Fin n) F := ⟨(A : Matrix (Fin n) (Fin n) F), hd⟩
  have hX : SpecialLinearGroup.toGL X = A := Units.ext rfl
  exact ⟨proj n F X, by rw [← CFSG.LieType.SeitzGeneration.conjAut_toGL, hX]⟩

theorem exists_inner_of_charThree (hn : 3 ≤ n) [CharP F 3] (A : GL (Fin n) F) (c : Fˣ)
    (hc : A ^ 3 = GeneralLinearGroup.scalar (Fin n) c) :
    ∃ k : projectiveSL n F, conjAut n F A = MulAut.conj k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective (fun x : F => x ^ 3) :=
    Finite.injective_iff_surjective.mp (frobenius_inj F 3)
  obtain ⟨γ, hγ⟩ := hsurj (c : F)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hγ]; norm_num)
  let S : GL (Fin n) F := GeneralLinearGroup.scalar (Fin n) (Units.mk0 γ⁻¹ (inv_ne_zero hγ0))
  have hS1 : conjAut n F S = 1 :=
    (ProjectivePlane.conjAut_eq_one_iff hn S).2 ⟨_, rfl⟩
  have hM3 : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ^ 3 =
      (c : F) • (1 : Matrix (Fin n) (Fin n) F) := by
    have e := congrArg (fun u : GL (Fin n) F => (u : Matrix (Fin n) (Fin n) F)) hc
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at e
    rw [e]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hA'm : ((S * A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      γ⁻¹ • ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hA'3 : (S * A) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hA'm, smul_pow, hM3, ← hγ, smul_smul, Units.val_one]
    have : γ⁻¹ ^ 3 * γ ^ 3 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hγ0, one_pow]
    rw [this, one_smul]
  have hdet3 : ((S * A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det ^ 3 = 1 := by
    have := congrArg (fun B : GL (Fin n) F => (B : Matrix (Fin n) (Fin n) F).det) hA'3
    simpa [Matrix.det_pow] using this
  have hdet1 : ((S * A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    set d := ((S * A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det
    have h0 : (d - 1) ^ 3 = 0 := by
      rw [sub_pow_char d 1, hdet3]; simp
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  obtain ⟨k, hk⟩ := conjAut_inner_of_det_eq_one hdet1
  exact ⟨k, by rw [map_mul, hS1, one_mul] at hk; exact hk⟩

theorem exists_fixed_perfect_three_of_diag (hn : 4 ≤ n) (A : GL (Fin n) F)
    (hA3 : conjAut n F A ^ 3 = 1) (hout : ∀ k : projectiveSL n F, conjAut n F A ≠ MulAut.conj k) :
    ∃ Q : Subgroup (projectiveSL n F), (∀ x ∈ Q, conjAut n F A x = x) ∧ ⁅Q, Q⁆ = Q ∧
      3 ∣ Nat.card Q := by
  obtain ⟨c, hc⟩ := (ProjectivePlane.conjAut_eq_one_iff (by omega) (A ^ 3)).mp
    (by rw [map_pow]; exact hA3)
  have h3 : (3 : F) ≠ 0 := by
    intro h3
    have : CharP F 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 (by exact_mod_cast h3)
    obtain ⟨k, hk⟩ := exists_inner_of_charThree (by omega) A c hc
    exact hout k hk
  have hK : 4 ≤ Nat.card F := by
    by_contra hlt
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h23 : Nat.card F = 2 ∨ Nat.card F = 3 := by omega
    rcases h23 with h2 | h2
    ·
      have hsub : Subsingleton Fˣ := by
        have : Nat.card Fˣ = 1 := by rw [Nat.card_units, h2]
        exact (Nat.card_eq_one_iff_unique.1 this).1
      have hdu : (Matrix.GeneralLinearGroup.det A : Fˣ) = 1 := Subsingleton.elim _ _
      have hd : (A : Matrix (Fin n) (Fin n) F).det = 1 := by
        have := congrArg Units.val hdu
        simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
      obtain ⟨k, hk⟩ := conjAut_inner_of_det_eq_one hd
      exact absurd hk (hout k)
    · apply h3
      let _ := Fintype.ofFinite F
      have := Nat.cast_card_eq_zero F
      rw [← Nat.card_eq_fintype_card, h2] at this
      exact_mod_cast this
  obtain ⟨a, ha, hE⟩ := exists_block_of_pow_three h3 hK c hc hn
  obtain ⟨Q, hQ, hQp, hQ3⟩ := exists_perfect_three_dvd_autFix_of_block h3
    (CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.squarefree_minpoly_linEnd_of_pow_scalar
      h3 c hc) a ha hE
  exact ⟨Q, hQ, hQp, hQ3⟩

end CFSG.HardMathSupport.Malle.E27Lie
