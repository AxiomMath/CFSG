module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpLev

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CGProof K421SpCWProof

section O3

@[expose] def P0F2 : Matrix (Fin 3) (Fin 3) F2 := !![1, 1, 0; 1, 1, 1; 1, 0, 1]

@[expose] def P0invF2 : Matrix (Fin 3) (Fin 3) F2 := !![1, 1, 1; 0, 1, 1; 1, 1, 0]

@[expose] def GF2 : Matrix (Fin 3) (Fin 3) F2 := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem P0F2_mul_inv : P0F2 * P0invF2 = 1 := by
  unfold P0F2 P0invF2
  decide +kernel

theorem P0invF2_mul : P0invF2 * P0F2 = 1 := by
  unfold P0F2 P0invF2
  decide +kernel

theorem P0F2_gram : P0F2ᵀ * P0F2 = GF2 := by
  unfold P0F2 GF2
  decide +kernel

variable {F : Type} [Field F] [CharP F 2]

@[expose] def P0 : Matrix (Fin 3) (Fin 3) F := P0F2.map (ι2 F)

@[expose] def P0inv : Matrix (Fin 3) (Fin 3) F := P0invF2.map (ι2 F)

@[expose] def Gm : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem P0_mul_inv : (P0 : Matrix (Fin 3) (Fin 3) F) * P0inv = 1 := by
  rw [P0, P0inv, ← Matrix.map_mul, P0F2_mul_inv]
  exact Matrix.map_one (ι2 F) (map_zero _) (map_one _)

theorem P0inv_mul : (P0inv : Matrix (Fin 3) (Fin 3) F) * P0 = 1 := by
  rw [P0, P0inv, ← Matrix.map_mul, P0invF2_mul]
  exact Matrix.map_one (ι2 F) (map_zero _) (map_one _)

theorem P0_gram : (P0 : Matrix (Fin 3) (Fin 3) F)ᵀ * P0 = Gm := by
  rw [P0, ← Matrix.transpose_map, ← Matrix.map_mul, P0F2_gram]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GF2, Gm]

@[expose] def ext1 (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, M 0 0, M 0 1; 0, M 1 0, M 1 1]

theorem ext1_mul (M N : Matrix (Fin 2) (Fin 2) F) : ext1 M * ext1 N = ext1 (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ext1, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem ext1_one : ext1 (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ext1]

theorem ext1_transpose (M : Matrix (Fin 2) (Fin 2) F) : (ext1 M)ᵀ = ext1 Mᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ext1]

theorem ext1_injective {M N : Matrix (Fin 2) (Fin 2) F} (h : ext1 M = ext1 N) : M = N := by
  ext i j
  have := congrFun (congrFun h i.succ) j.succ
  fin_cases i <;> fin_cases j <;> simpa [ext1] using this

theorem ext1_J : ext1 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) = Gm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ext1, Gm]

@[expose] def omat (A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  P0 * ext1 (A : Matrix (Fin 2) (Fin 2) F) * P0inv

theorem omat_mul (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    omat A * omat B = omat (A * B) := by
  have h : omat A * omat B = P0 * (ext1 (A : Matrix (Fin 2) (Fin 2) F) *
      ((P0inv * P0) * ext1 (B : Matrix (Fin 2) (Fin 2) F))) * P0inv := by
    unfold omat
    noncomm_ring
  rw [h, P0inv_mul, one_mul, ext1_mul]
  unfold omat
  rw [Matrix.SpecialLinearGroup.coe_mul]

theorem omat_one : omat (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  unfold omat
  rw [Matrix.SpecialLinearGroup.coe_one, ext1_one, Matrix.mul_one, P0_mul_inv]

theorem omat_orth (A : Matrix.SpecialLinearGroup (Fin 2) F) : (omat A)ᵀ * omat A = 1 := by
  have hEGE : (ext1 (A : Matrix (Fin 2) (Fin 2) F))ᵀ * Gm * ext1 (A : Matrix (Fin 2) (Fin 2) F) =
      Gm := by
    rw [ext1_transpose, ← ext1_J, ext1_mul, ext1_mul, sl2_symp]
  calc (omat A)ᵀ * omat A
      = (P0inv : Matrix (Fin 3) (Fin 3) F)ᵀ * ((ext1 (A : Matrix (Fin 2) (Fin 2) F))ᵀ *
          ((P0 : Matrix (Fin 3) (Fin 3) F)ᵀ * P0) * ext1 (A : Matrix (Fin 2) (Fin 2) F)) * P0inv := by
        unfold omat
        simp only [Matrix.transpose_mul]
        noncomm_ring
    _ = (P0inv : Matrix (Fin 3) (Fin 3) F)ᵀ * Gm * P0inv := by
        rw [P0_gram, hEGE]
    _ = (P0 * P0inv : Matrix (Fin 3) (Fin 3) F)ᵀ * (P0 * P0inv) := by
        rw [← P0_gram]
        simp only [Matrix.transpose_mul]
        noncomm_ring
    _ = 1 := by
        rw [P0_mul_inv]
        simp

@[expose] def o3 : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(SpI F) :=
  spHom (fun A => levMat (omat A) (omat A))
    (fun A B => by rw [levMat_mul, omat_mul])
    (by rw [omat_one, levMat_one])
    (fun A => levMat_symp (omat_orth A) (omat_orth A))

theorem o3_val (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((o3 A : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) = levMat (omat A) (omat A) := rfl

theorem o3_injective : Function.Injective (o3 (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro A h
  have h1 : levMat (omat A) (omat A) = levMat 1 1 := by
    rw [levMat_one, ← o3_val]
    exact congrArg (fun y : ↥(SpI F) => ((y : GL Idx F) : Matrix Idx Idx F)) h
  have h2 : omat A = 1 := levMat_inj_left h1
  have h3 : ext1 (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h5 : P0inv * omat A * P0 = ext1 (A : Matrix (Fin 2) (Fin 2) F) := by
      calc P0inv * omat A * P0
          = (P0inv * P0) * ext1 (A : Matrix (Fin 2) (Fin 2) F) * (P0inv * P0) := by
            unfold omat
            noncomm_ring
        _ = ext1 (A : Matrix (Fin 2) (Fin 2) F) := by
            rw [P0inv_mul]
            simp
    rw [← h5, h2]
    simp [P0inv_mul]
  have h4 : (A : Matrix (Fin 2) (Fin 2) F) = 1 := ext1_injective (h3.trans ext1_one.symm)
  exact Subtype.ext (by simpa using h4)

theorem o3_mem_centralizer_rep2 (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    o3 A ∈ Subgroup.centralizer ({(monoSp F).av (rep 2)} : Set ↥(SpI F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  apply Subtype.ext
  apply Units.ext
  show ((((monoSp F).av (rep 2) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) *
      ((o3 A : ↥(SpI F)) : GL Idx F).val = ((o3 A : ↥(SpI F)) : GL Idx F).val *
        ((((monoSp F).av (rep 2) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F)
  rw [av_rep2, o3_val]
  refine (levMat_comm_bd3 ?_).symm
  intro i j s t
  have hC : ∀ k : Fin 3, (![tm F 0 1, tm F 0 1, tm F 0 1] k) = tm F 0 1 := by
    intro k
    fin_cases k <;> rfl
  simp only [ite_self, hC]
  ring

theorem rankOneAt_rep2 [Finite F] {p : ℕ}
    (hp : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) :
    RankOneAt p ((monoSp F).av (rep 2)) :=
  ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, inferInstance, o3, o3_injective,
    by
      rintro _ ⟨A, rfl⟩
      exact o3_mem_centralizer_rep2 A,
    hp⟩

theorem simpleAt_rep2 [Finite F] {p : ℕ} (hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hp : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F))
    (hne : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ≠ p) :
    SimpleAt p ((monoSp F).av (rep 2)) :=
  ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, inferInstance, hS, o3, o3_injective,
    by
      rintro _ ⟨A, rfl⟩
      exact o3_mem_centralizer_rep2 A,
    hp, hne⟩

end O3

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
