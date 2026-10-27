module

public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.K72L3Fix

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

section Elements

variable {K : Type} [Field K]

private theorem exists_cyc_negSwap :
    ∃ C W : Matrix (Fin 3) (Fin 3) K, C.det = 1 ∧ W.det = 1 ∧ C * (C * C) = 1 ∧ W * W = 1 ∧
      W * C * W = C * C ∧ Cᵀ * C = 1 ∧ Wᵀ * W = 1 ∧ C ≠ 1 ∧
      ∀ φ : K →+* K, C.map φ = C ∧ W.map φ = W := by
  refine ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![-1, 0, 0; 0, 0, -1; 0, -1, 0], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, fun h => by simpa using congrFun (congrFun h 0) 0, fun φ => ⟨?_, ?_⟩⟩
  · rw [det_fin_three]
    simp
  · rw [det_fin_three]
    simp
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_sl_three_inverting_anyChar :
    ∃ c w : SpecialLinearGroup (Fin 3) K, c ^ 3 = 1 ∧ c ≠ 1 ∧ w * c * w⁻¹ = c⁻¹ ∧
      (∀ σ : K ≃+* K, SpecialLinearGroup.map σ.toRingHom c = c) ∧
      (∀ σ : K ≃+* K, SpecialLinearGroup.map σ.toRingHom w = w) := by
  obtain ⟨C, W, hCdet, hWdet, hC3, hWW, hWCW, -, -, hC1, hmap⟩ := exists_cyc_negSwap (K := K)
  set c : SpecialLinearGroup (Fin 3) K := ⟨C, hCdet⟩
  set w : SpecialLinearGroup (Fin 3) K := ⟨W, hWdet⟩
  have hc3 : c * (c * c) = 1 := Subtype.ext hC3
  refine ⟨c, w, by rw [pow_three]; exact hc3, fun h => hC1 (congrArg Subtype.val h), ?_,
    fun σ => Subtype.ext (hmap σ.toRingHom).1, fun σ => Subtype.ext (hmap σ.toRingHom).2⟩
  rw [inv_eq_of_mul_eq_one_right (Subtype.ext hWW : w * w = 1),
    (Subtype.ext hWCW : w * c * w = c * c)]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_assoc]; exact hc3)

theorem exists_fieldAut_fixed_inverting_anyChar (hK : Nat.card K % 3 = 2) (σ : K ≃+* K) :
    ∃ x₀ y₀ : projectiveSL 3 K, fieldAut 3 K σ x₀ = x₀ ∧ fieldAut 3 K σ y₀ = y₀ ∧
      x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨c, w, hc3, hc1, hwc, hcσ, hwσ⟩ := exists_sl_three_inverting_anyChar (K := K)
  refine ⟨proj 3 K c, proj 3 K w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fieldAut_proj, hcσ]
  · rw [fieldAut_proj, hwσ]
  · rw [← map_pow, hc3, map_one]
  · intro h
    exact hc1 (proj_three_injective hK (h.trans (map_one _).symm))
  · rw [← map_inv, ← map_mul, ← map_mul, hwc, map_inv]

variable {p f : ℕ}

theorem exists_unitarySU_three_inverting_anyChar (h : UnitaryFieldData p f K) :
    ∃ c w : unitarySU p f K 3, c ^ 3 = 1 ∧ c ≠ 1 ∧ w * c * w⁻¹ = c⁻¹ ∧
      (∀ σ : K ≃+* K, suField h σ c = c) ∧ (∀ σ : K ≃+* K, suField h σ w = w) := by
  obtain ⟨C, W, hCdet, hWdet, hC3, hWW, hWCW, hCt, hWt, hC1, hmap⟩ := exists_cyc_negSwap (K := K)
  have hcmem : (⟨C, C * C, hC3, by rw [Matrix.mul_assoc, hC3]⟩ : GL (Fin 3) K) ∈
      unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨hCdet, ?_⟩
    change (C.map h.bar)ᵀ * C = 1
    rw [(hmap h.bar).1, hCt]
  have hwmem : (⟨W, W, hWW, hWW⟩ : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨hWdet, ?_⟩
    change (W.map h.bar)ᵀ * W = 1
    rw [(hmap h.bar).2, hWt]
  set c : unitarySU p f K 3 := ⟨_, hcmem⟩
  set w : unitarySU p f K 3 := ⟨_, hwmem⟩
  have hc3 : c * (c * c) = 1 := Subtype.ext (Units.ext hC3)
  refine ⟨c, w, by rw [pow_three]; exact hc3,
    fun h1 => hC1 (congrArg (fun A : unitarySU p f K 3 => ((A : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) h1), ?_, fun σ => ?_, fun σ => ?_⟩
  · rw [inv_eq_of_mul_eq_one_right (Subtype.ext (Units.ext hWW) : w * w = 1),
      (Subtype.ext (Units.ext hWCW) : w * c * w = c * c)]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_assoc]; exact hc3)
  · apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    exact (hmap σ.toRingHom).1
  · apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    exact (hmap σ.toRingHom).2

theorem exists_psuField_fixed_inverting_anyChar (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) (σ : K ≃+* K) :
    ∃ x₀ y₀ : unitaryPSU h 3, psuField h σ x₀ = x₀ ∧ psuField h σ y₀ = y₀ ∧
      x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨c, w, hc3, hc1, hwc, hcσ, hwσ⟩ := exists_unitarySU_three_inverting_anyChar h
  refine ⟨unitaryProj h 3 c, unitaryProj h 3 w, ?_, ?_, ?_, ?_, ?_⟩
  · exact (psuField_mk σ c).trans (congrArg (unitaryProj h 3) (hcσ σ))
  · exact (psuField_mk σ w).trans (congrArg (unitaryProj h 3) (hwσ σ))
  · rw [← map_pow, hc3, map_one]
  · intro h1
    exact hc1 (unitaryProj_three_injective h hq (h1.trans (map_one _).symm))
  · rw [← map_inv, ← map_mul, ← map_mul, hwc, map_inv]

end Elements

theorem fixedData_linear_anyChar {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    (∃ M : ℕ, (∀ T : Subgroup (projectiveSL 3 K), (∀ t ∈ T, fieldAut 3 K σ t = t) →
      Nat.card T ∣ M) ∧ 3 * M ∣ Nat.card (projectiveSL 3 K)) ∧
      ∃ x₀ y₀ : projectiveSL 3 K, fieldAut 3 K σ x₀ = x₀ ∧ fieldAut 3 K σ y₀ = y₀ ∧
        x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ :=
  ⟨⟨_, card_dvd_of_forall_fieldAut_eq hK σ, three_mul_card_dvd_linear hK hσ⟩,
    exists_fieldAut_fixed_inverting_anyChar hK σ⟩

theorem fixedData_unitary_anyChar {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    (∃ M : ℕ, (∀ T : Subgroup (unitaryPSU h 3), (∀ t ∈ T, psuField h σ t = t) →
      Nat.card T ∣ M) ∧ 3 * M ∣ Nat.card (unitaryPSU h 3)) ∧
      ∃ x₀ y₀ : unitaryPSU h 3, psuField h σ x₀ = x₀ ∧ psuField h σ y₀ = y₀ ∧
        x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p f₀ (GH74.GLS.IVK.fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  exact ⟨⟨_, card_dvd_of_forall_psuField_eq h hq hf h₀, three_mul_card_dvd_unitary h hq hf h₀⟩,
    exists_psuField_fixed_inverting_anyChar h hq σ⟩

theorem fixedData_of_mulEquiv_projSL_anyChar {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K)
    (α : MulAut X) (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨σ, hσ, τ, hτ⟩ := exists_congr_eq_fieldAut_of_mulEquiv_projSL hK e hα hout
  obtain ⟨h₁, h₂⟩ := fixedData_linear_anyChar hK hσ
  rw [← hτ] at h₁ h₂
  exact fixedData_of_congr τ α h₁ h₂

theorem fixedData_of_mulEquiv_projSU_of_ne_zero {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (hf : f ≠ 0) (hq : p ^ f % 3 = 1) (e : X ≃* CFSG.Assembly.RankThreeEven.projSU 3 p f)
    (α : MulAut X) (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  have h : UnitaryFieldData p f (GaloisField p (2 * f)) :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, GaloisField.card p (2 * f) (by omega)⟩
  obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  have hq2 : 2 < p ^ f := by
    have h2 : 2 ≤ p ^ f := (Fact.out : p.Prime).two_le.trans (Nat.le_self_pow hf p)
    omega
  obtain ⟨σ, hσ, τ, hτ⟩ :=
    exists_congr_eq_psuField_of_mulEquiv_unitaryPSU h hq hq2 (e.trans φ.symm) hα hout
  obtain ⟨h₁, h₂⟩ := fixedData_unitary_anyChar h hq hσ
  rw [← hτ] at h₁ h₂
  exact fixedData_of_congr τ α h₁ h₂

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
