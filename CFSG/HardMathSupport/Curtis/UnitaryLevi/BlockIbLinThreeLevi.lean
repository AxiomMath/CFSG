module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbLinThreeAut
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi.LinA

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def leviMat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem leviMat_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    leviMat (A * B) = leviMat A * leviMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem leviMat_one : leviMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat]

theorem det_leviMat (A : Matrix (Fin 2) (Fin 2) K) : (leviMat A).det = A.det := by
  simp [leviMat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def leviEmb : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨leviMat (A : Matrix (Fin 2) (Fin 2) K), by rw [det_leviMat]; exact A.2⟩
  map_one' := by
    apply Subtype.ext
    simp [leviMat_one]
  map_mul' A B := by
    apply Subtype.ext
    show leviMat ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      leviMat (A : Matrix (Fin 2) (Fin 2) K) * leviMat (B : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, leviMat_mul]

theorem coe_leviEmb (A : SpecialLinearGroup (Fin 2) K) :
    ((leviEmb A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      leviMat (A : Matrix (Fin 2) (Fin 2) K) := rfl

theorem leviEmb_mem_stabilizer (A : SpecialLinearGroup (Fin 2) K) :
    leviEmb A ∈ stabilizer (flagSpace 3 K 1) := by
  rw [mem_stabilizer, flagSpace_one_eq_span, Submodule.map_span, Set.image_singleton]
  have : mulVecLin ((leviEmb A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      (Pi.single 0 1) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp [coe_leviEmb, leviMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.single_apply]
  rw [this]

section Perfect

variable [Finite K]

theorem leviHom_injective :
    Function.Injective ((proj 3 K).comp (leviEmb (K := K))) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.comp_apply] at hA
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hA)
  have h00 : ((leviEmb A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    simp [coe_leviEmb, leviMat]
  rw [hc] at h00
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00
  have h1 : leviEmb A = 1 := by
    apply Subtype.ext
    rw [hc]
    have : (c : K) = 1 := h00
    simp [this]
  have hinj : Function.Injective (leviEmb (K := K)) := by
    intro A B hAB
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hAB
    simp only [coe_leviEmb, leviMat] at this
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun this (i.succ)) (j.succ)
    fin_cases i <;> fin_cases j <;> simpa using this
  exact hinj (by rw [h1, map_one])

theorem exists_levi_perfect (hK : ∃ s : Finset K, s.card = 4) :
    ∃ V : Subgroup (projectiveSL 3 K), V ≤ projStabilizer (flagSpace 3 K 1) ∧ ⁅V, V⁆ = V ∧
      Nat.card K ^ 2 - 1 ∣ Nat.card V := by
  set f : SpecialLinearGroup (Fin 2) K →* projectiveSL 3 K := (proj 3 K).comp leviEmb with hf
  haveI := CFSG.LinearGroups.special_linear_dimension_two_perfect hK
  refine ⟨f.range, ?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact ⟨leviEmb A, leviEmb_mem_stabilizer A, rfl⟩
  · exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range f)
  · have h1 : Nat.card f.range = Nat.card (SpecialLinearGroup (Fin 2) K) :=
      (Nat.card_congr (MonoidHom.ofInjective (leviHom_injective (K := K))).toEquiv).symm
    rw [h1, card_SL_eq (by norm_num : 1 ≤ 2)]
    simp

end Perfect

section Duality

variable [CharP K 2] [Finite K]

@[expose] def wMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem wMat_mul_self : (wMat : Matrix (Fin 3) (Fin 3) K) * wMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def wGL : GL (Fin 3) K := ⟨wMat, wMat, wMat_mul_self, wMat_mul_self⟩

theorem map_dotOrth_flagSpace_two :
    (dotOrth (flagSpace 3 K 2)).map
      (mulVecLin (((wGL : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) = flagSpace 3 K 1 := by
  ext v
  rw [Submodule.mem_map, mem_flagSpace]
  constructor
  · rintro ⟨u, hu, rfl⟩ j hj
    rw [mem_dotOrth] at hu
    have h0 : u 0 = 0 := by
      have := hu (Pi.single 0 1) (by rw [mem_flagSpace_two_iff]; simp)
      simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
    have h1 : u 1 = 0 := by
      have := hu (Pi.single 1 1) (by rw [mem_flagSpace_two_iff]; simp)
      simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using this
    fin_cases j
    · simp at hj
    · simp [wGL, wMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1]
    · simp [wGL, wMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0]
  · intro hv
    refine ⟨![0, 0, v 0], ?_, ?_⟩
    · rw [mem_dotOrth]
      intro w hw
      rw [mem_flagSpace_two_iff] at hw
      simp [dotProduct, Fin.sum_univ_three, hw]
    · ext i
      have h1 := hv 1 (by simp)
      have h2 := hv 2 (by simp)
      fin_cases i <;> simp [wGL, wMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

theorem exists_aut_plane_to_point :
    ∃ κ : MulAut (projectiveSL 3 K), (projStabilizer (flagSpace 3 K 2)).map κ.toMonoidHom =
      projStabilizer (flagSpace 3 K 1) := by
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  have h7 : ∀ (B : GL (Fin 3) K) (W : Submodule K (Fin 3 → K)),
      (projStabilizer W).map (conjAut 3 K B).toMonoidHom =
        projStabilizer (W.map (mulVecLin (B : Matrix (Fin 3) (Fin 3) K))) :=
    htrans.2.2.2.2.2.2.1
  have h9 : ∀ W : Submodule K (Fin 3 → K),
      (projStabilizer W).map (dualAut 3 K).toMonoidHom = projStabilizer (dotOrth W) :=
    htrans.2.2.2.2.2.2.2.2.1
  refine ⟨conjAut 3 K wGL * dualAut 3 K, ?_⟩
  rw [map_toMonoidHom_mul', h9, h7, map_dotOrth_flagSpace_two]

end Duality

end CFSG.HardMathSupport.Curtis.UnitaryLevi.LinA
