module

import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Supp
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K]

private theorem pow_three_of_conj_diagonal (h : UnitaryFieldData 2 1 K)
    {X R : primeFormUnitary h (idGram K 6)} {v : Fin 6 → K} (hv : ∀ i, v i ^ 3 = 1)
    (hR : (((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal v) : X ^ 3 = 1 := by
  rw [← conj_eq_one_iff (a := R), ← conj_pow]
  refine Subtype.ext (Units.ext ?_)
  change ((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K).val ^ 3 = 1
  rw [hR, diagonal_pow, ← diagonal_one]
  exact congrArg diagonal (funext hv)

private theorem commute_of_conj_diagonal (h : UnitaryFieldData 2 1 K)
    {X Y R : primeFormUnitary h (idGram K 6)} {v w : Fin 6 → K}
    (hX : (((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal v)
    (hY : (((R * Y * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal w) : X * Y = Y * X := by
  have e : (R * X * R⁻¹) * (R * Y * R⁻¹) = (R * Y * R⁻¹) * (R * X * R⁻¹) := by
    refine Subtype.ext (Units.ext ?_)
    change ((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K).val *
        ((R * Y * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K).val =
      ((R * Y * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K).val *
        ((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K).val
    rw [hX, hY, diagonal_mul_diagonal, diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)
  calc X * Y = R⁻¹ * ((R * X * R⁻¹) * (R * Y * R⁻¹)) * R := by group
    _ = R⁻¹ * ((R * Y * R⁻¹) * (R * X * R⁻¹)) * R := by rw [e]
    _ = Y * X := by group

private theorem mul_diagonal_eq_of_conj (h : UnitaryFieldData 2 1 K)
    {X R Q : primeFormUnitary h (idGram K 6)} {ξ v : Fin 6 → K}
    (hξ : (((Q⁻¹ * X * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ξ)
    (hv : (((R * X * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal v) :
    (((R * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        diagonal ξ = diagonal v *
      (((R * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
  rw [← hξ, ← hv]
  have e : (R * Q) * (Q⁻¹ * X * Q) = (R * X * R⁻¹) * (R * Q) := by group
  exact congrArg
    (fun g : primeFormUnitary h (idGram K 6) => ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) e

theorem exists_common_frame_six (h : UnitaryFieldData 2 1 K) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {D X₁ X₂ R : primeFormUnitary h (idGram K 6)} (hD3 : D ^ 3 = 1)
    (hDX₁ : D * X₁ = X₁ * D) (hDX₂ : D * X₂ = X₂ * D)
    (hR₁ : (((R * X₁ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ω, 1])
    (hR₂ : (((R * X₂ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, 1, ω]) :
    ∃ (Q : primeFormUnitary h (idGram K 6)) (δ : Fin 6 → K) (k₁ k₂ : Fin 6), k₁ ≠ k₂ ∧
      (((Q⁻¹ * D * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal δ ∧
      (((Q⁻¹ * X₁ * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = (diagonal fun i => if i = k₁ then ω else 1) ∧
      (((Q⁻¹ * X₂ * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal fun i => if i = k₂ then ω else 1 := by
  classical
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hX₁3 : X₁ ^ 3 = 1 := pow_three_of_conj_diagonal h (fun i => by
    fin_cases i <;> simp [hω3]) hR₁
  have hX₂3 : X₂ ^ 3 = 1 := pow_three_of_conj_diagonal h (fun i => by
    fin_cases i <;> simp [hω3]) hR₂
  have hX₁₂ : X₁ * X₂ = X₂ * X₁ := commute_of_conj_diagonal h hR₁ hR₂
  obtain ⟨P, hP, hPd⟩ := CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj
    h (by norm_num) {(D : GL (Fin 6) K), (X₁ : GL (Fin 6) K), (X₂ : GL (Fin 6) K)}
    (by rintro x (rfl | rfl | rfl) <;> first | exact D.2 | exact X₁.2 | exact X₂.2)
    (by
      rintro x (rfl | rfl | rfl) z (rfl | rfl | rfl) <;>
        first | rfl | exact congrArg Subtype.val hDX₁ | exact (congrArg Subtype.val hDX₁).symm |
          exact congrArg Subtype.val hDX₂ | exact (congrArg Subtype.val hDX₂).symm |
          exact congrArg Subtype.val hX₁₂ | exact (congrArg Subtype.val hX₁₂).symm)
    (by
      rintro x (rfl | rfl | rfl)
      · exact congrArg Subtype.val hD3
      · exact congrArg Subtype.val hX₁3
      · exact congrArg Subtype.val hX₂3)
  obtain ⟨Q, rfl⟩ : ∃ Q : primeFormUnitary h (idGram K 6), (Q : GL (Fin 6) K) = P := ⟨⟨P, hP⟩, rfl⟩
  have hdD := hPd (D : GL (Fin 6) K) (Set.mem_insert _ _)
  obtain ⟨ξ₁, hξ₁⟩ : ∃ ξ : Fin 6 → K, (((Q⁻¹ * X₁ * Q : primeFormUnitary h (idGram K 6)) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal ξ :=
    ⟨_, (hPd (X₁ : GL (Fin 6) K) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))).diagonal_diag.symm⟩
  obtain ⟨ξ₂, hξ₂⟩ : ∃ ξ : Fin 6 → K, (((Q⁻¹ * X₂ * Q : primeFormUnitary h (idGram K 6)) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal ξ :=
    ⟨_, (hPd (X₂ : GL (Fin 6) K)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))).diagonal_diag.symm⟩
  have hdet : (((R * Q : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K).det ≠ 0 := (Matrix.isUnits_det_units _).ne_zero
  obtain ⟨π, hπ⟩ := CFSG.LocalAnalysis.GLTheoremA.S265BU8.exists_perm_of_support hdet
    (a := fun j => (ξ₁ j, ξ₂ j))
    (a' := fun l => ((![1, 1, 1, 1, ω, 1] : Fin 6 → K) l, (![1, 1, 1, 1, 1, ω] : Fin 6 → K) l))
    (fun l k hlk => Prod.ext
      (CFSG.LocalAnalysis.GLTheoremA.S265BU8.eq_of_mul_diagonal_eq
        (mul_diagonal_eq_of_conj h hξ₁ hR₁) hlk)
      (CFSG.LocalAnalysis.GLTheoremA.S265BU8.eq_of_mul_diagonal_eq
        (mul_diagonal_eq_of_conj h hξ₂ hR₂) hlk))
  have hv₁ : ∀ l : Fin 6, (![1, 1, 1, 1, ω, 1] : Fin 6 → K) l = if l = 4 then ω else 1 :=
    fun l => by fin_cases l <;> simp
  have hv₂ : ∀ l : Fin 6, (![1, 1, 1, 1, 1, ω] : Fin 6 → K) l = if l = 5 then ω else 1 :=
    fun l => by fin_cases l <;> simp
  refine ⟨Q, _, π.symm 4, π.symm 5, fun h45 => absurd (π.symm.injective h45) (by norm_num),
    hdD.diagonal_diag.symm, ?_, ?_⟩
  · rw [hξ₁]
    refine congrArg diagonal (funext fun k => ?_)
    have e1 : (![1, 1, 1, 1, ω, 1] : Fin 6 → K) (π k) = ξ₁ k := congrArg Prod.fst (hπ k)
    rw [← e1, hv₁]
    exact if_congr (Equiv.apply_eq_iff_eq_symm_apply π) rfl rfl
  · rw [hξ₂]
    refine congrArg diagonal (funext fun k => ?_)
    have e2 : (![1, 1, 1, 1, 1, ω] : Fin 6 → K) (π k) = ξ₂ k := congrArg Prod.snd (hπ k)
    rw [← e2, hv₂]
    exact if_congr (Equiv.apply_eq_iff_eq_symm_apply π) rfl rfl

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
