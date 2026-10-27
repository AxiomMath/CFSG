module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def heisClosure (ℓ f : ℕ) (K : Type) [Field K] (ω : K) : Subgroup (unitarySU ℓ f K 3) :=
  Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ heisLines ω, ∃ c : K,
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
      c • (M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))}

theorem unitaryHeisCore_iff : UnitaryHeisCore ↔
    ∀ (ℓ f : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
      ∀ ω : K, IsPrimitiveRoot ω 3 → heisClosure ℓ f K ω = ⊤ :=
  Iff.rfl

@[expose] def blockOneMat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem blockOneMat_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    blockOneMat (A * B) = blockOneMat A * blockOneMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockOneMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blockOneMat_one : blockOneMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockOneMat]

@[expose] def blockOneHom : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := blockOneMat
  map_one' := blockOneMat_one
  map_mul' := blockOneMat_mul

@[expose] def blockOneGL : GL (Fin 2) K →* GL (Fin 3) K :=
  Units.map blockOneHom

theorem coe_blockOneGL (A : GL (Fin 2) K) :
    ((blockOneGL A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockOneMat (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] def heisB12 (ℓ f : ℕ) (K : Type) [Field K] : Subgroup (unitarySU ℓ f K 3) :=
  ((unitarySU ℓ f K 2).map blockOneGL).subgroupOf (unitarySU ℓ f K 3)

theorem mem_heisB12 {g : unitarySU ℓ f K 3} :
    g ∈ heisB12 ℓ f K ↔ ∃ A : GL (Fin 2) K, A ∈ unitarySU ℓ f K 2 ∧
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        !![(A : Matrix (Fin 2) (Fin 2) K) 0 0, (A : Matrix (Fin 2) (Fin 2) K) 0 1, 0;
          (A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1, 0; 0, 0, 1] := by
  rw [heisB12, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨A, hA, hg⟩
    exact ⟨A, hA, by rw [← hg]; rfl⟩
  · rintro ⟨A, hA, hg⟩
    exact ⟨A, hA, Units.ext hg.symm⟩

end CFSG.LieType.SeitzGeneration
