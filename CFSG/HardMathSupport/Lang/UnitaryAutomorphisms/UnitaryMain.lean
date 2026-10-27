module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.FieldCase
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.DiagNonCube

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem scalar_mem_primeFormUnitary (h : UnitaryFieldData p f K) {x : K} (hx0 : x ≠ 0)
    (hx : h.bar x * x = 1) :
    GeneralLinearGroup.scalar (Fin n) (Units.mk0 x hx0) ∈
      primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [mem_primeFormUnitary]
  ext i j
  simp only [GeneralLinearGroup.coe_scalar, Units.val_one, Units.val_mk0, Matrix.mul_one,
    Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.mul_apply, Matrix.diagonal_apply, hx]
  · simp [Matrix.mul_apply, Matrix.diagonal_apply, hij]

theorem hasFixedThreePair_or_irred (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (hn : 3 ≤ n) (hn3 : 3 ∣ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hβ3 : β ^ 3 = 1)
    (hβi : β ∉ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    HasFixedThreePair β ∨
      (n = 3 ∧ ∃ B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        β = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) B ∧
        ∃ l : K, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
            l • (1 : Matrix (Fin n) (Fin n) K) ∧ ∀ x : K, x ^ 3 ≠ l) := by
  classical
  have hfin := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGL
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq β
  rw [primeFormPsi_apply] at hAφ
  have hφ : primeFormFieldFactor h hC hn hq β = φ := by
    rw [← hAφ]
    exact primeFormFieldFactor_apply h hC hn hq A φ
  by_cases hψ : primeFormFieldFactor h hC hn hq β = 1
  swap
  · exact Or.inl (hasFixedThreePair_of_fieldFactor_ne_one h h3 hn hq β hβ3 hψ)
  rw [hφ] at hψ
  have hβA : β = primeFormConjHom h _ A := by
    rw [← hAφ, hψ, map_one, mul_one]
  have hA3 : primeFormConjHom h _ (A ^ 3) = 1 := by
    rw [map_pow, ← hβA]
    exact hβ3
  obtain ⟨-, c, hc1, hcA⟩ := (primeFormPsi_eq_one_iff h hC hn
    (⟨A ^ 3, 1⟩ : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC]
      (K ≃+* K))).mp (by
        rw [primeFormPsi_apply, map_one, mul_one]
        exact hA3)
  set Am : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hM3 : Am ^ 3 = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    have e := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hcA
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.coe_scalar] at e
    rw [hAm, e]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hcN : h.bar (c : K) * (c : K) = 1 := by
    have := hc1
    rw [UnitaryFieldData.norm] at this
    rw [mul_comm]; exact this
  have hl1 : (c : K) ^ (p ^ f + 1) = 1 := by
    rw [pow_succ, ← h.bar_apply, mul_comm]
    exact hc1
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, pow_mul']
  by_cases hcube : ∃ x : K, x ^ 3 = (c : K)
  · obtain ⟨x, hx1, hx3⟩ := (CFSG.HardMathSupport.Lang.Proving.cube_normOne_iff hK h3 hl1).2 hcube
    have hx0 : x ≠ 0 := by
      rintro rfl
      have : (c : K) = 0 := by rw [← hx3]; norm_num
      exact c.ne_zero this
    have hxn : h.bar x * x = 1 := by
      rw [h.bar_apply, ← pow_succ]; exact hx1
    have hxi : h.bar x⁻¹ * x⁻¹ = 1 := by
      rw [map_inv₀, ← mul_inv, hxn, inv_one]
    have hxi0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
    have hs := scalar_mem_primeFormUnitary (n := n) h hxi0 hxi
    let S : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, hs⟩
    have hS1 : primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) S = 1 := by
      have := (primeFormPsi_eq_one_iff h hC hn
        (⟨S, 1⟩ : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC]
          (K ≃+* K))).mpr ⟨rfl, Units.mk0 x⁻¹ hxi0, by
            rw [UnitaryFieldData.norm, mul_comm]; exact hxi, rfl⟩
      rw [primeFormPsi_apply, map_one, mul_one] at this
      exact this
    set A' : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := S * A with hA'
    have hA'm : ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = x⁻¹ • Am := by
      rw [hA']
      show (GeneralLinearGroup.scalar (Fin n) (Units.mk0 x⁻¹ hxi0) * (A : GL (Fin n) K) :
        GL (Fin n) K).val = _
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    have hA'3 : (A' : GL (Fin n) K) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hA'm, smul_pow, hM3, ← hx3, smul_smul, Units.val_one]
      have : x⁻¹ ^ 3 * x ^ 3 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow]
      rw [this, one_smul]
    have hβA' : β = primeFormConjHom h _ A' := by
      rw [hA', map_mul, hS1, one_mul, hβA]
    have hdet : n = 3 → ((A' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ≠ 1 := by
      intro _ hd1
      have hmem : (A' : GL (Fin n) K) ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        (mem_gramSU_iff_unitary h).mpr ⟨A'.2, hd1⟩
      exact hβi ((mem_inner_primeFormP h _ β).2 ⟨⟨(A' : GL (Fin n) K), hmem⟩, hβA'⟩)
    refine Or.inl ?_
    rw [hβA']
    exact hasFixedThreePair_diag_of_pow_three h h3 hn A' hA'3 hdet
  · have hnc : ∀ x : K, x ^ 3 ≠ (c : K) := fun x hx => hcube ⟨x, hx⟩
    by_cases hn6 : 6 ≤ n
    · exact Or.inl (by
        rw [hβA]
        exact hasFixedThreePair_diag_of_nonCube h h3 hn6 A hM3 hnc)
    · have hn3' : n = 3 := by
        obtain ⟨k, hk⟩ := hn3
        omega
      exact Or.inr ⟨hn3', A, hβA, (c : K), hM3, hnc⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
