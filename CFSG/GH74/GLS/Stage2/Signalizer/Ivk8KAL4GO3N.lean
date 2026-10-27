module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAOrth

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open scoped MatrixGroups commutatorElement

theorem ka_orthData_nonsplit_three {K : Type} [Field K] [Finite K] (h3 : Nat.card K = 3)
    (R : GL (Fin 4) K) (hR : (R : Matrix (Fin 4) (Fin 4) K)ᵀ = R)
    (hns : ¬ ∃ S : Submodule K (Fin 4 → K), Module.finrank K ↥S = 2 ∧
      ∀ x ∈ S, matrixQuadraticForm R x = 0) :
    OrthComponentData 4 K R := by
  have hK : ringChar K ≠ 2 := ka_ringChar_ne_two_of_card_three h3
  have hodd := odd_card_of_ringChar_ne_two K hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Q := matrixQuadraticForm R with hQ
  have hQnd := polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  set e := isoOrthGL hK R hR with he
  by_cases hT : ∃ T : Submodule K (Fin 4 → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    have hq := CatalogueBOrthogonal.derived_quasisimple Q h2 hQnd hT3.ge hTQ
    have hq' := isQuasisimple_trans e hq
    rw [trans_commutator] at hq'
    refine ⟨commutator_eq_self_of_isQuasisimple hq', 1,
      fun _ => ⁅CatalogueBGraphForm.isometryGroup 4 K R, CatalogueBGraphForm.isometryGroup 4 K R⁆,
      by simp, fun _ => ⟨hq', le_rfl, ?_⟩⟩
    intro x hx l hl
    exact mul_mem (mul_mem hx hl) (inv_mem hx)
  · have hcases := CatalogueBOrthogonalAssembly.low_Witt_finrank_cases hodd Q hQnd
      (by rw [hdim]; norm_num) hT
    rw [hdim] at hcases
    have hcase : (Odd (Nat.card K) ∧ (Module.finrank K (Fin 4 → K) = 3 ∨
        Module.finrank K (Fin 4 → K) = 4 ∨ Module.finrank K (Fin 4 → K) = 5)) ∨
        (Odd (Nat.card K) ∧ Module.finrank K (Fin 4 → K) = 6 ∧
          ¬ ∃ T : Submodule K (Fin 4 → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
        (Module.finrank K (Fin 4 → K) = 4 ∧
          ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :=
      Or.inl ⟨hodd, Or.inr (Or.inl hdim)⟩
    have hne : ¬ ((Module.finrank K (Fin 4 → K) = 3 ∧ Nat.card K = 3) ∨
        ((Module.finrank K (Fin 4 → K) = 4 ∧
          ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
          (Nat.card K = 2 ∨ Nat.card K = 3))) := by
      rintro (⟨h4, -⟩ | ⟨⟨-, hS⟩, -⟩)
      · omega
      · exact hns hS
    obtain ⟨hperf, -, ⟨m, L, -, -, hsup, hL, -⟩, -⟩ :=
      (LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
        Q hQnd hcase).2.1 hne
    refine ⟨commutator_trans_of_isPerfect e hperf, m, fun i => transportGL e (L i), ?_,
      fun i =>
      ⟨isQuasisimple_trans e (hL i).1, trans_le_commutator e (hL i).2.1, fun x hx l hl =>
        conj_mem_trans e (hL i).2.1 (hL i).2.2 hx hl⟩⟩
    rw [← trans_iSup, hsup, trans_commutator]

theorem ka_quadraticForm_congr {K : Type} [Field K] {R R' : GL (Fin 4) K}
    {P : Matrix (Fin 4) (Fin 4) K}
    (hP : Pᵀ * (R : Matrix (Fin 4) (Fin 4) K) * P = R') (x : Fin 4 → K) :
    matrixQuadraticForm R (Matrix.toLin' P x) = matrixQuadraticForm R' x := by
  have h := Matrix.toBilin'_comp (R : Matrix (Fin 4) (Fin 4) K) P P
  rw [hP] at h
  have h2 := LinearMap.congr_fun₂ h x x
  simpa [matrixQuadraticForm, matrixForm] using h2

theorem ka_noSplit_congr {K : Type} [Field K] {R R' P : GL (Fin 4) K}
    (hP : (P : Matrix (Fin 4) (Fin 4) K)ᵀ * (R : Matrix (Fin 4) (Fin 4) K) * P = R')
    (hns : ¬ ∃ S : Submodule K (Fin 4 → K), Module.finrank K ↥S = 2 ∧
      ∀ x ∈ S, matrixQuadraticForm R x = 0) :
    ¬ ∃ S : Submodule K (Fin 4 → K), Module.finrank K ↥S = 2 ∧
      ∀ x ∈ S, matrixQuadraticForm R' x = 0 := by
  rintro ⟨S, hS2, hSQ⟩
  apply hns
  have hinj : Function.Injective (Matrix.toLin' (P : Matrix (Fin 4) (Fin 4) K)) := by
    intro x y hxy
    have hxy' : (P : Matrix (Fin 4) (Fin 4) K) *ᵥ x = (P : Matrix (Fin 4) (Fin 4) K) *ᵥ y := hxy
    have := congrArg (fun v => ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) hxy'
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  refine ⟨S.map (Matrix.toLin' (P : Matrix (Fin 4) (Fin 4) K)), ?_, ?_⟩
  · rw [← (Submodule.equivMapOfInjective _ hinj S).finrank_eq]
    exact hS2
  · rintro _ ⟨x, hx, rfl⟩
    rw [ka_quadraticForm_congr hP x]
    exact hSQ x hx

theorem kaL4GOrthThreeNS_thm :
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 → ∀ A : GL (Fin 4) F,
      (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A → ¬ KAL4Split A →
      KAAll (conjAut 4 F A * dualAut 4 F) := by
  intro F _ _ h3 A hA hns
  have hK : ringChar F ≠ 2 := ka_ringChar_ne_two_of_card_three h3
  refine ka_all_of_orth (by norm_num) hK A hA ?_
  rintro w hw ⟨P, hP⟩
  have hsym : ((diagGL hw.1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = diagGL hw.1 := by
    rw [coe_diagGL, diagonal_transpose]
  refine ka_orthData_nonsplit_three h3 _ hsym (ka_noSplit_congr (R := A⁻¹) (P := P) ?_ hns)
  rw [coe_diagGL]
  exact hP

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
