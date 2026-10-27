module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResB
public import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.HDescUniRes CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield mem_fixSubfield)
open Matrix

variable {K : Type} [Field K]

private theorem apply_three {σ : K ≃+* K} (hσ : orderOf σ = 3) (x : K) : σ (σ (σ x)) = x := by
  have h1 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have h2 : (σ ^ 3) x = σ (σ (σ x)) := rfl
  rw [← h2, h1]
  rfl

private theorem card_fixSubfield (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : Nat.card (fixSubfield σ) = 4 :=
  (dvd_and_card_fixSubfield_unitary h Nat.prime_three (by norm_num) hσ).2.trans (by norm_num)

private theorem map_eq_of_pow_three (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {x : K} (hx : x ^ 3 = 1) : σ x = x := by
  have := h.finite
  have h3 : 3 ∣ Nat.card (fixSubfield σ) - 1 := by rw [card_fixSubfield h hσ] <;> norm_num
  obtain ⟨ω, hω⟩ := CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd h3
  have hωK : IsPrimitiveRoot (ω : K) 3 := hω.map_of_injective (fixSubfield σ).subtype.injective
  obtain ⟨m, -, rfl⟩ := hωK.eq_pow_of_pow_eq_one hx
  rw [map_pow, (mem_fixSubfield σ).1 ω.2]

private theorem pow_three_eq_one_of_map_eq (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {x : K} (hx0 : x ≠ 0) (hx : σ x = x) : x ^ 3 = 1 := by
  have := h.finite
  have hy : (⟨x, (mem_fixSubfield σ).2 hx⟩ : fixSubfield σ) ≠ 0 := fun h0 =>
    hx0 (congrArg Subtype.val h0)
  have hu : Units.mk0 _ hy ^ Nat.card (fixSubfield σ)ˣ = 1 := pow_card_eq_one'
  rw [Nat.card_units, card_fixSubfield h hσ] at hu
  simpa using congrArg (fun u : (fixSubfield σ)ˣ => ((u : fixSubfield σ) : K)) hu

private theorem pow_three_eq_one_of_norm (h : UnitaryFieldData 2 3 K) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {l : K} (hl0 : l ≠ 0) (hl9 : l ^ 9 = 1)
    (hN : l * (σ l * σ (σ l)) = 1) : l ^ 3 = 1 := by
  set ε := σ l / l with hε
  have hεl : σ l = ε * l := by rw [hε, div_mul_cancel₀ _ hl0]
  have hε3 : ε ^ 3 = 1 := by
    rw [hε, div_pow, ← map_pow, map_eq_of_pow_three h hσ (by rw [← pow_mul]; exact hl9),
      div_self (pow_ne_zero 3 hl0)]
  have hσσ : σ (σ l) = ε * (ε * l) := by rw [hεl, map_mul, map_eq_of_pow_three h hσ hε3, hεl]
  rw [hσσ, hεl] at hN
  linear_combination hN - l ^ 3 * hε3

private theorem exists_cube_root (h : UnitaryFieldData 2 3 K) {α : Kˣ} (hα : (α : K) ^ 3 = 1) :
    ∃ μ : Kˣ, μ ^ 9 = 1 ∧ μ ^ 3 = α := by
  have := h.finite
  have h9 : 9 ∣ Nat.card K - 1 := by rw [h.card]; norm_num
  obtain ⟨ζ, hζ⟩ := CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd h9
  have hζ3 : IsPrimitiveRoot (ζ ^ 3) 3 := hζ.pow_of_dvd (by norm_num) (by norm_num)
  obtain ⟨i, -, hi⟩ := hζ3.eq_pow_of_pow_eq_one hα
  refine ⟨Units.mk0 ζ (hζ.ne_zero (by norm_num)) ^ i, ?_, ?_⟩
  · ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [← hi, ← pow_mul, ← pow_mul, mul_comm]

theorem exists_cube_lift_of_fieldHom_comm (h : UnitaryFieldData 2 3 K) {n : ℕ} (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {c : MulAut (primeFormP h (idGram K n))}
    (hcD : c ∈ primeFormD h (idGram K n)) (hc3 : c ^ 3 = 1)
    (hcσ : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ * c =
      c * primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ) :
    ∃ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X = c ∧ X ^ 3 = 1 := by
  have hne : ¬(n = 3 ∧ 2 ^ 3 = 2) := by norm_num
  obtain ⟨A, α, -, hA3, rfl⟩ := exists_pow_scalar_of_mem_primeFormD hn hcD hc3
  have hz : primeFormConjHom h (idGram K n)
      (A⁻¹ * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := n)) σ A) = 1 := by
    rw [map_mul, map_inv,
      ← primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := n)) σ A, hcσ,
      mul_inv_cancel_right, inv_mul_cancel]
  obtain ⟨lam, hlam9, hlam⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).1 hz
  have hσA : glAut σ (A : GL (Fin n) K) =
      (A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) lam := by
    rw [← hlam, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, mul_inv_cancel_left]
  let i0 : Fin n := ⟨0, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i0 j ≠ 0 := by
    by_contra hall
    push Not at hall
    have e := congrFun (congrFun (A : GL (Fin n) K).mul_inv i0) i0
    simp [Matrix.mul_apply, hall] at e
  have hσa : σ (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i0 j) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i0 j * lam := by
    have e := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i0 j) hσA
    simpa only [coe_glAut, Matrix.map_apply, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, mul_diagonal] using e
  have h3a := apply_three hσ (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i0 j)
  rw [hσa, map_mul, hσa, map_mul, map_mul, hσa] at h3a
  have hN : (lam : K) * (σ lam * σ (σ lam)) = 1 := by
    apply mul_left_cancel₀ hj
    rw [mul_one]
    linear_combination h3a
  have hl9 : (lam : K) ^ 9 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hlam9
  have hl3 := pow_three_eq_one_of_norm h hσ lam.ne_zero hl9 hN
  have hcom : Commute (A : GL (Fin n) K) (GeneralLinearGroup.scalar (Fin n) lam) :=
    (GeneralLinearGroup.scalar_commute lam _).symm
  have e : glAut σ (GeneralLinearGroup.scalar (Fin n) α) =
      GeneralLinearGroup.scalar (Fin n) (α * lam ^ 3) := by
    rw [← hA3, map_pow, hσA, hcom.mul_pow, hA3, map_mul, map_pow]
  have e' := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i0 i0) e
  simp only [coe_glAut, Matrix.map_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_apply_eq, Units.val_mul, Units.val_pow_eq_pow_val] at e'
  rw [hl3, mul_one] at e'
  obtain ⟨μ, hμ9, hμ3⟩ := exists_cube_root h (pow_three_eq_one_of_map_eq h hσ α.ne_zero e')
  have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
    rw [← pow_succ_eq_one_iff_norm h, inv_pow, show 2 ^ 3 + 1 = 9 by norm_num, hμ9, inv_one]
  have hAμ : (A : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) (μ ^ 3) := by
    rw [hA3, hμ3]
  exact ⟨scalarU h n μ⁻¹ hμ'n * A, by rw [map_mul, conjHom_scalarU hn hne, one_mul],
    rescale_pow_eq_one hn hne hμ'n hAμ⟩

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
