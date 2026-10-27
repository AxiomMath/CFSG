module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResG
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (IsGood)
open Matrix
open CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

private theorem card_units_four {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) :
    Nat.card Kˣ = 3 := by
  have := Nat.card_units K
  rw [h.card] at this
  simpa using this

private theorem units_pow_three_four {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) (u : Kˣ) :
    u ^ 3 = 1 := by
  rw [← card_units_four h]
  exact pow_card_eq_one'

private theorem norm_eq_one_four {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) (u : Kˣ) :
    h.norm (u : K) = 1 :=
  (pow_succ_eq_one_iff_norm h u).mp (units_pow_three_four h u)

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem exists_frame_six_of_twoGroup (h : UnitaryFieldData 2 1 K) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {A V : Subgroup (MulAut (primeFormP h (idGram K 6)))}
    (hA : IsElemAbelian 3 A) (h81 : 3 ^ 4 ≤ Nat.card A) (hAD : A ≤ primeFormD h (idGram K 6))
    (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥) (hVD : V ≤ primeFormD h (idGram K 6))
    (hAV : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) :
    ∃ X₁ X₂ R : primeFormUnitary h (idGram K 6),
      primeFormConjHom h (idGram K 6) X₁ ∈ A ∧ primeFormConjHom h (idGram K 6) X₂ ∈ A ∧
      (((R * X₁ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, ω, 1] ∧
      (((R * X₂ * R⁻¹ : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal ![1, 1, 1, 1, 1, ω] := by
  classical
  have hne : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    exact one_ne_zero (by linear_combination hω - h2 : (1 : K) = 0)
  let Â : Subgroup (primeFormUnitary h (idGram K 6)) := A.comap (primeFormConjHom h (idGram K 6))
  have hmemÂ : ∀ X, X ∈ Â ↔ primeFormConjHom h (idGram K 6) X ∈ A := fun X => Iff.rfl
  obtain ⟨T₂, hT₂2, hT₂, hT₂U, hT₂N⟩ :=
    S265BU8.exists_two_lift_of_le_primeFormD h (by norm_num) (by norm_num) hV2 hV hVD hAV
  let ÂG : Subgroup (GL (Fin 6) K) := Â.map (primeFormUnitary h (idGram K 6)).subtype
  have hÂGU : ÂG ≤ primeFormUnitary h (idGram K 6) := Subgroup.map_subtype_le Â
  obtain ⟨W, hW, hWiso, hWÂ⟩ := exists_isotropic_stable h hT₂2 hT₂ hT₂U hÂGU (by
    rintro _ ⟨X, hX, rfl⟩ t ht
    exact hT₂N X hX t ht)
  have hscÂ : ∀ μ : Kˣ, scalarU h 6 μ (norm_eq_one_four h μ) ∈ Â := fun μ => by
    rw [hmemÂ, conjHom_scalarU (by norm_num) hne]
    exact one_mem A
  have hÂ3 : IsPGroup 3 ÂG := by
    rintro ⟨_, X, hX, rfl⟩
    refine ⟨2, ?_⟩
    have h1 : primeFormConjHom h (idGram K 6) (X ^ 3) = 1 := by
      rw [map_pow]
      exact hA.2 _ ((hmemÂ X).1 hX)
    obtain ⟨z, -, hz⟩ := (primeFormConjHom_eq_one_iff_of_ne (by norm_num) hne _).1 h1
    have e : (X : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) z := by
      rw [← Subgroup.coe_pow, hz]
    apply Subtype.ext
    show (X : GL (Fin 6) K) ^ (3 ^ 2) = 1
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, e, ← map_pow, units_pow_three_four h z,
      map_one]
  have hcard : 81 < Nat.card ÂG := by
    rw [Subgroup.card_map_of_injective (primeFormUnitary h (idGram K 6)).subtype_injective]
    let ψ : Â →* A := MonoidHom.codRestrict ((primeFormConjHom h (idGram K 6)).comp Â.subtype) A
      (fun X => X.2)
    have hψs : Function.Surjective ψ := by
      rintro ⟨a, ha⟩
      obtain ⟨X, rfl⟩ := hAD ha
      exact ⟨⟨X, ha⟩, rfl⟩
    have hker : ψ.ker ≠ ⊥ := by
      intro hbot
      have hmem : (⟨_, hscÂ (Units.mk0 ω hω0)⟩ : Â) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext (conjHom_scalarU (by norm_num) hne (Units.mk0 ω hω0)
          (norm_eq_one_four h _))
      rw [hbot, Subgroup.mem_bot] at hmem
      have e := congrArg (fun X : Â => (((X : primeFormUnitary h (idGram K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) 0 0) hmem
      simp [coe_scalarU, hω1] at e
    have h2 : 2 ≤ Nat.card ψ.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 hker
    rw [← Subgroup.card_ker_mul_card_of_surjective hψs]
    calc 81 < 2 * 3 ^ 4 := by norm_num
      _ ≤ Nat.card ψ.ker * Nat.card A := Nat.mul_le_mul h2 h81
  obtain ⟨w, hw0, hwW, hwX⟩ := exists_common_eigenvector_six h hÂ3 hÂGU hcard hW hWiso hWÂ
  have hwiso : idForm h 6 w w = 0 := Submodule.mem_orthogonalBilin_iff.mp (hWiso hwW) w hwW
  exact exists_frame_six h hω hA h81 hAD hw0 hwiso (fun X hX => hwX _ ⟨X, hX, rfl⟩)

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
