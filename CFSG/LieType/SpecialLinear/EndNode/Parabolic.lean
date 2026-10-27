module

public import CFSG.LieType.SpecialLinear.EndNode.Radicals
public import CFSG.LieType.SpecialLinear.EndNode.Blocks

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

@[expose] def blockEquivLast : Fin (m+1) ⊕ Fin 1 ≃ Fin (m+2) :=
  finSumFinEquiv

@[expose] def fromBlocksLast (A : Matrix (Fin (m+1)) (Fin (m+1)) F)
    (B : Matrix (Fin (m+1)) (Fin 1) F) (C : Matrix (Fin 1) (Fin (m+1)) F)
    (D : Matrix (Fin 1) (Fin 1) F) : Matrix (Fin (m+2)) (Fin (m+2)) F :=
  Matrix.reindexAlgEquiv F F (blockEquivLast m) (Matrix.fromBlocks A B C D)

private theorem blockEquivLast_symm_castSucc (i : Fin (m+1)) :
    (blockEquivLast m).symm i.castSucc = Sum.inl i := by
  rw [blockEquivLast]
  exact finSumFinEquiv_symm_apply_castAdd i

private theorem blockEquivLast_symm_last :
    (blockEquivLast m).symm (Fin.last (m+1)) = Sum.inr 0 := by
  rw [blockEquivLast]
  have h : (Fin.last (m+1) : Fin (m+2)) = Fin.natAdd (m+1) (0 : Fin 1) := by
    ext
    simp [Fin.natAdd, Fin.last]
  rw [h, finSumFinEquiv_symm_apply_natAdd]

omit [Finite F] in
theorem fromBlocksLast_apply_castSucc_castSucc {A : Matrix (Fin (m+1)) (Fin (m+1)) F}
    {B : Matrix (Fin (m+1)) (Fin 1) F} {C : Matrix (Fin 1) (Fin (m+1)) F}
    {D : Matrix (Fin 1) (Fin 1) F} (i j : Fin (m+1)) :
    fromBlocksLast m F A B C D i.castSucc j.castSucc = A i j := by
  simp [fromBlocksLast, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivLast_symm_castSucc, Matrix.fromBlocks_apply₁₁]

omit [Finite F] in
theorem fromBlocksLast_apply_castSucc_last {A : Matrix (Fin (m+1)) (Fin (m+1)) F}
    {B : Matrix (Fin (m+1)) (Fin 1) F} {C : Matrix (Fin 1) (Fin (m+1)) F}
    {D : Matrix (Fin 1) (Fin 1) F} (i : Fin (m+1)) :
    fromBlocksLast m F A B C D i.castSucc (Fin.last (m+1)) = B i 0 := by
  simp [fromBlocksLast, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivLast_symm_castSucc, blockEquivLast_symm_last,
    Matrix.fromBlocks_apply₁₂]

omit [Finite F] in
theorem fromBlocksLast_apply_last_castSucc {A : Matrix (Fin (m+1)) (Fin (m+1)) F}
    {B : Matrix (Fin (m+1)) (Fin 1) F} {C : Matrix (Fin 1) (Fin (m+1)) F}
    {D : Matrix (Fin 1) (Fin 1) F} (j : Fin (m+1)) :
    fromBlocksLast m F A B C D (Fin.last (m+1)) j.castSucc = C 0 j := by
  simp [fromBlocksLast, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivLast_symm_castSucc, blockEquivLast_symm_last,
    Matrix.fromBlocks_apply₂₁]

omit [Finite F] in
theorem fromBlocksLast_apply_last_last {A : Matrix (Fin (m+1)) (Fin (m+1)) F}
    {B : Matrix (Fin (m+1)) (Fin 1) F} {C : Matrix (Fin 1) (Fin (m+1)) F}
    {D : Matrix (Fin 1) (Fin 1) F} :
    fromBlocksLast m F A B C D (Fin.last (m+1)) (Fin.last (m+1)) = D 0 0 := by
  simp [fromBlocksLast, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivLast_symm_last, Matrix.fromBlocks_apply₂₂]

omit [Finite F] in
private theorem fromBlocksLast_mul (A : Matrix (Fin (m+1)) (Fin (m+1)) F)
    (B : Matrix (Fin (m+1)) (Fin 1) F) (C : Matrix (Fin 1) (Fin (m+1)) F)
    (D : Matrix (Fin 1) (Fin 1) F) (A' : Matrix (Fin (m+1)) (Fin (m+1)) F)
    (B' : Matrix (Fin (m+1)) (Fin 1) F) (C' : Matrix (Fin 1) (Fin (m+1)) F)
    (D' : Matrix (Fin 1) (Fin 1) F) :
    fromBlocksLast m F A B C D * fromBlocksLast m F A' B' C' D' =
      fromBlocksLast m F (A * A' + B * C') (A * B' + B * D') (C * A' + D * C')
        (C * B' + D * D') := by
  rw [fromBlocksLast, fromBlocksLast, fromBlocksLast, ← map_mul,
    Matrix.fromBlocks_multiply]

omit [Finite F] in
private theorem fromBlocksFirst_mul (A : Matrix (Fin 1) (Fin 1) F)
    (B : Matrix (Fin 1) (Fin (m+1)) F) (C : Matrix (Fin (m+1)) (Fin 1) F)
    (D : Matrix (Fin (m+1)) (Fin (m+1)) F) (A' : Matrix (Fin 1) (Fin 1) F)
    (B' : Matrix (Fin 1) (Fin (m+1)) F) (C' : Matrix (Fin (m+1)) (Fin 1) F)
    (D' : Matrix (Fin (m+1)) (Fin (m+1)) F) :
    fromBlocksFirst m F A B C D * fromBlocksFirst m F A' B' C' D' =
      fromBlocksFirst m F (A * A' + B * C') (A * B' + B * D') (C * A' + D * C')
        (C * B' + D * D') := by
  rw [fromBlocksFirst, fromBlocksFirst, fromBlocksFirst, ← map_mul,
    Matrix.fromBlocks_multiply]

@[expose] def bottomPartFirst (g : SLm2 m F) :
    Matrix (Fin (m+1)) (Fin (m+1)) F :=
  Matrix.of fun i j => (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i.succ j.succ

@[expose] def rowPart (g : SLm2 m F) : Matrix (Fin 1) (Fin (m+1)) F :=
  Matrix.of fun _ j => (g : Matrix (Fin (m+2)) (Fin (m+2)) F) 0 j.succ

@[expose] def colPart (g : SLm2 m F) : Matrix (Fin (m+1)) (Fin 1) F :=
  Matrix.of fun i _ => (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i.succ 0

@[expose] def bottomPartLast (g : SLm2 m F) :
    Matrix (Fin (m+1)) (Fin (m+1)) F :=
  Matrix.of fun i j => (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i.castSucc j.castSucc

@[expose] def lastColPart (g : SLm2 m F) : Matrix (Fin (m+1)) (Fin 1) F :=
  Matrix.of fun i _ => (g : Matrix (Fin (m+2)) (Fin (m+2)) F) i.castSucc (Fin.last (m+1))

@[expose] def lastRowPart (g : SLm2 m F) : Matrix (Fin 1) (Fin (m+1)) F :=
  Matrix.of fun _ j => (g : Matrix (Fin (m+2)) (Fin (m+2)) F) (Fin.last (m+1)) j.castSucc

omit [Finite F] in
theorem coe_eq_fromBlocksFirst_of_mem_firstRow {g : SLm2 m F}
    (hg : g ∈ firstRowRadical m F) :
    (g : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 (rowPart m F g) 0 1 := by
  obtain ⟨h00, hrow⟩ := (mem_rowRadical (m := m) (F := F)).mp hg
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [h00]
    rw [fromBlocksFirst_apply_zero_zero (A := 1) (B := rowPart m F g) (C := 0)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    simp
  · rw [fromBlocksFirst_apply_zero_succ (A := 1) (B := rowPart m F g) (C := 0)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    rfl
  · rw [hrow i.succ 0 (by simp), Matrix.one_apply_ne (by simp)]
    rw [fromBlocksFirst_apply_succ_zero (A := 1) (B := rowPart m F g) (C := 0)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    rfl
  · rw [hrow i.succ j.succ (by simp), Matrix.one_apply]
    rw [fromBlocksFirst_apply_succ_succ (A := 1) (B := rowPart m F g) (C := 0)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    simp [Matrix.one_apply, Fin.succ_inj]

omit [Finite F] in
theorem coe_eq_fromBlocksFirst_of_mem_firstCol {g : SLm2 m F}
    (hg : g ∈ firstColRadical m F) :
    (g : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 (colPart m F g) 1 := by
  obtain ⟨h00, hcol⟩ := (mem_colRadical (m := m) (F := F)).mp hg
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [h00]
    rw [fromBlocksFirst_apply_zero_zero (A := 1) (B := 0) (C := colPart m F g)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    simp
  · rw [hcol 0 j.succ (by simp), Matrix.one_apply_ne (by simp)]
    rw [fromBlocksFirst_apply_zero_succ (A := 1) (B := 0) (C := colPart m F g)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    rfl
  · rw [fromBlocksFirst_apply_succ_zero (A := 1) (B := 0) (C := colPart m F g)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    rfl
  · rw [hcol i.succ j.succ (by simp), Matrix.one_apply]
    rw [fromBlocksFirst_apply_succ_succ (A := 1) (B := 0) (C := colPart m F g)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    simp [Matrix.one_apply, Fin.succ_inj]

omit [Finite F] in
theorem coe_eq_fromBlocksLast_of_mem_lastCol {g : SLm2 m F}
    (hg : g ∈ lastColRadical m F) :
    (g : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F 1 (lastColPart m F g) 0 1 := by
  obtain ⟨h00, hcol⟩ := (mem_colRadical (m := m) (F := F)).mp hg
  ext i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · rw [hcol i.castSucc j.castSucc (by simp), Matrix.one_apply]
    rw [fromBlocksLast_apply_castSucc_castSucc (A := 1) (B := lastColPart m F g)
      (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp [Matrix.one_apply]
  · rw [fromBlocksLast_apply_castSucc_last (A := 1) (B := lastColPart m F g)
      (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [hcol (Fin.last (m+1)) j.castSucc (by simp), Matrix.one_apply_ne (by simp)]
    rw [fromBlocksLast_apply_last_castSucc (A := 1) (B := lastColPart m F g)
      (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [h00]
    rw [fromBlocksLast_apply_last_last (A := 1) (B := lastColPart m F g)
      (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp

omit [Finite F] in
theorem coe_eq_fromBlocksLast_of_mem_lastRow {g : SLm2 m F}
    (hg : g ∈ lastRowRadical m F) :
    (g : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F 1 0 (lastRowPart m F g) 1 := by
  obtain ⟨h00, hrow⟩ := (mem_rowRadical (m := m) (F := F)).mp hg
  ext i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · rw [hrow i.castSucc j.castSucc (by simp), Matrix.one_apply]
    rw [fromBlocksLast_apply_castSucc_castSucc (A := 1) (B := 0)
      (C := lastRowPart m F g) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp [Matrix.one_apply]
  · rw [hrow i.castSucc (Fin.last (m+1)) (by simp), Matrix.one_apply_ne (by simp)]
    rw [fromBlocksLast_apply_castSucc_last (A := 1) (B := 0)
      (C := lastRowPart m F g) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [fromBlocksLast_apply_last_castSucc (A := 1) (B := 0)
      (C := lastRowPart m F g) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [h00]
    rw [fromBlocksLast_apply_last_last (A := 1) (B := 0)
      (C := lastRowPart m F g) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp

omit [Fact (Nat.Prime p)] in
private theorem det_bottomPartFirst_of_mem_U {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).U) :
    (bottomPartFirst m F u).det = 1 := by
  have hu' := (mem_curtisDatum_U_iff (m := m+1) (F := F) (p := p)).mp hu
  have hUT : (bottomPartFirst m F u).IsUpperTriangular := by
    intro i j hji
    exact hu'.2 i.succ j.succ (by simpa using hji)
  rw [Matrix.det_of_isUpperTriangular hUT]
  exact Finset.prod_eq_one fun i _ => hu'.1 i.succ

omit [Fact (Nat.Prime p)] in
private theorem det_bottomPartFirst_of_mem_L {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).L) :
    (bottomPartFirst m F u).det = 1 := by
  have hu' := (mem_curtisDatum_L_iff (m := m+1) (F := F) (p := p)).mp hu
  have hLT : (bottomPartFirst m F u).IsLowerTriangular := by
    intro i j hij
    exact hu'.2 i.succ j.succ (by simpa using hij)
  rw [Matrix.det_of_lowerTriangular _ hLT]
  exact Finset.prod_eq_one fun i _ => hu'.1 i.succ

omit [Fact (Nat.Prime p)] in
private theorem det_bottomPartLast_of_mem_U {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).U) :
    (bottomPartLast m F u).det = 1 := by
  have hu' := (mem_curtisDatum_U_iff (m := m+1) (F := F) (p := p)).mp hu
  have hUT : (bottomPartLast m F u).IsUpperTriangular := by
    intro i j hji
    exact hu'.2 i.castSucc j.castSucc (by simpa using hji)
  rw [Matrix.det_of_isUpperTriangular hUT]
  exact Finset.prod_eq_one fun i _ => hu'.1 i.castSucc

omit [Fact (Nat.Prime p)] in
private theorem det_bottomPartLast_of_mem_L {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).L) :
    (bottomPartLast m F u).det = 1 := by
  have hu' := (mem_curtisDatum_L_iff (m := m+1) (F := F) (p := p)).mp hu
  have hLT : (bottomPartLast m F u).IsLowerTriangular := by
    intro i j hij
    exact hu'.2 i.castSucc j.castSucc (by simpa using hij)
  rw [Matrix.det_of_lowerTriangular _ hLT]
  exact Finset.prod_eq_one fun i _ => hu'.1 i.castSucc

omit [Fact (Nat.Prime p)] in
private theorem bottomPartFirst_mem_U {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).U) :
    (⟨bottomPartFirst m F u, det_bottomPartFirst_of_mem_U m F p hu⟩ : SLm1 m F) ∈
      (curtisDatum m F p).U := by
  let a : SLm1 m F :=
    ⟨bottomPartFirst m F u, det_bottomPartFirst_of_mem_U m F p hu⟩
  change a ∈ (curtisDatum m F p).U
  have hu' := (mem_curtisDatum_U_iff (m := m+1) (F := F) (p := p)).mp hu
  rw [mem_curtisDatum_U_iff]
  exact ⟨fun i => hu'.1 i.succ, fun i j hji => hu'.2 i.succ j.succ (by simpa using hji)⟩

omit [Fact (Nat.Prime p)] in
private theorem bottomPartLast_mem_U {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).U) :
    (⟨bottomPartLast m F u, det_bottomPartLast_of_mem_U m F p hu⟩ : SLm1 m F) ∈
      (curtisDatum m F p).U := by
  let a : SLm1 m F :=
    ⟨bottomPartLast m F u, det_bottomPartLast_of_mem_U m F p hu⟩
  change a ∈ (curtisDatum m F p).U
  have hu' := (mem_curtisDatum_U_iff (m := m+1) (F := F) (p := p)).mp hu
  rw [mem_curtisDatum_U_iff]
  exact ⟨fun i => hu'.1 i.castSucc, fun i j hji => hu'.2 i.castSucc j.castSucc (by simpa using hji)⟩

omit [Fact (Nat.Prime p)] in
private theorem coe_eq_fromBlocksFirst_of_mem_U {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).U) :
    (u : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 (rowPart m F u) 0 (bottomPartFirst m F u) := by
  have hu' := (mem_curtisDatum_U_iff (m := m+1) (F := F) (p := p)).mp hu
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [hu'.1 0]
    rw [fromBlocksFirst_apply_zero_zero (A := 1) (B := rowPart m F u) (C := 0)
      (D := bottomPartFirst m F u)]
    simp
  · rw [fromBlocksFirst_apply_zero_succ (A := 1) (B := rowPart m F u) (C := 0)
      (D := bottomPartFirst m F u)]
    rfl
  · rw [fromBlocksFirst_apply_succ_zero (A := 1) (B := rowPart m F u) (C := 0)
      (D := bottomPartFirst m F u)]
    rw [hu'.2 i.succ 0 (by simp)]
    simp
  · rw [fromBlocksFirst_apply_succ_succ (A := 1) (B := rowPart m F u) (C := 0)
      (D := bottomPartFirst m F u)]
    rfl

omit [Fact (Nat.Prime p)] in
private theorem coe_eq_fromBlocksFirst_of_mem_L {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).L) :
    (u : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 (colPart m F u) (bottomPartFirst m F u) := by
  have hu' := (mem_curtisDatum_L_iff (m := m+1) (F := F) (p := p)).mp hu
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rw [hu'.1 0]
    rw [fromBlocksFirst_apply_zero_zero (A := 1) (B := 0) (C := colPart m F u)
      (D := bottomPartFirst m F u)]
    simp
  · rw [fromBlocksFirst_apply_zero_succ (A := 1) (B := 0) (C := colPart m F u)
      (D := bottomPartFirst m F u)]
    rw [hu'.2 0 j.succ (by simp)]
    simp
  · rw [fromBlocksFirst_apply_succ_zero (A := 1) (B := 0) (C := colPart m F u)
      (D := bottomPartFirst m F u)]
    rfl
  · rw [fromBlocksFirst_apply_succ_succ (A := 1) (B := 0) (C := colPart m F u)
      (D := bottomPartFirst m F u)]
    rfl

omit [Fact (Nat.Prime p)] in
private theorem coe_eq_fromBlocksLast_of_mem_U {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).U) :
    (u : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F (bottomPartLast m F u) (lastColPart m F u) 0 1 := by
  have hu' := (mem_curtisDatum_U_iff (m := m+1) (F := F) (p := p)).mp hu
  ext i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · rw [fromBlocksLast_apply_castSucc_castSucc (A := bottomPartLast m F u)
      (B := lastColPart m F u) (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [fromBlocksLast_apply_castSucc_last (A := bottomPartLast m F u)
      (B := lastColPart m F u) (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [fromBlocksLast_apply_last_castSucc (A := bottomPartLast m F u)
      (B := lastColPart m F u) (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rw [hu'.2 (Fin.last (m+1)) j.castSucc (by simp)]
    simp
  · rw [hu'.1 (Fin.last (m+1))]
    rw [fromBlocksLast_apply_last_last (A := bottomPartLast m F u)
      (B := lastColPart m F u) (C := 0) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp

omit [Fact (Nat.Prime p)] in
private theorem coe_eq_fromBlocksLast_of_mem_L {u : SLm2 m F}
    (hu : u ∈ (curtisDatum (m+1) F p).L) :
    (u : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F (bottomPartLast m F u) 0 (lastRowPart m F u) 1 := by
  have hu' := (mem_curtisDatum_L_iff (m := m+1) (F := F) (p := p)).mp hu
  ext i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · rw [fromBlocksLast_apply_castSucc_castSucc (A := bottomPartLast m F u) (B := 0)
      (C := lastRowPart m F u) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [fromBlocksLast_apply_castSucc_last (A := bottomPartLast m F u)
      (B := (0 : Matrix (Fin (m+1)) (Fin 1) F)) (C := lastRowPart m F u)
      (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rw [hu'.2 i.castSucc (Fin.last (m+1)) (by simp)]
    simp
  · rw [fromBlocksLast_apply_last_castSucc (A := bottomPartLast m F u) (B := 0)
      (C := lastRowPart m F u) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    rfl
  · rw [hu'.1 (Fin.last (m+1))]
    rw [fromBlocksLast_apply_last_last (A := bottomPartLast m F u) (B := 0)
      (C := lastRowPart m F u) (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp

omit [Finite F] in
theorem coe_embedSucc_eq_fromBlocksFirst (a : SLm1 m F) :
    (embedSucc m F a : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 0 (a : Matrix (Fin (m+1)) (Fin (m+1)) F) := rfl

omit [Finite F] in
theorem coe_embedCastSucc_eq_fromBlocksLast (a : SLm1 m F) :
    (embedCastSucc m F a : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F (a : Matrix (Fin (m+1)) (Fin (m+1)) F) 0 0 1 := by
  rw [coe_embedCastSucc]
  change Matrix.blockSucc (a : Matrix (Fin (m+1)) (Fin (m+1)) F) =
    fromBlocksLast m F (a : Matrix (Fin (m+1)) (Fin (m+1)) F) 0 0 1
  ext i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · rw [fromBlocksLast_apply_castSucc_castSucc]
    exact Matrix.blockSucc_castSucc_castSucc _ i j
  · rw [fromBlocksLast_apply_castSucc_last]
    exact Matrix.blockSucc_castSucc_last _ i
  · rw [fromBlocksLast_apply_last_castSucc]
    exact Matrix.blockSucc_last_castSucc _ j
  · rw [fromBlocksLast_apply_last_last]
    simp

omit [Finite F] in
@[simp] theorem coe_mul_coe_inv (a : SLm1 m F) :
    (a : Matrix (Fin (m+1)) (Fin (m+1)) F) *
      ((a⁻¹ : SLm1 m F) : Matrix (Fin (m+1)) (Fin (m+1)) F) = 1 := by
  have h := congrArg (fun x : SLm1 m F =>
    (x : Matrix (Fin (m+1)) (Fin (m+1)) F)) (mul_inv_cancel a)
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h

omit [Finite F] in
@[simp] theorem coe_inv_mul_coe (a : SLm1 m F) :
    ((a⁻¹ : SLm1 m F) : Matrix (Fin (m+1)) (Fin (m+1)) F) *
      (a : Matrix (Fin (m+1)) (Fin (m+1)) F) = 1 := by
  have h := congrArg (fun x : SLm1 m F =>
    (x : Matrix (Fin (m+1)) (Fin (m+1)) F)) (inv_mul_cancel a)
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h

omit [Finite F] in
private theorem mem_firstRowRadical_of_blocks {B : Matrix (Fin 1) (Fin (m+1)) F}
    {x : SLm2 m F}
    (hx : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 B 0 1) :
    x ∈ firstRowRadical m F := by
  rw [mem_rowRadical]
  constructor
  · rw [hx]
    rw [fromBlocksFirst_apply_zero_zero (A := 1) (B := B) (C := 0)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    simp
  · intro i j hi
    rw [hx]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · exact absurd rfl hi
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rw [fromBlocksFirst_apply_succ_zero (A := 1) (B := B) (C := 0)
        (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
      rfl
    · rw [fromBlocksFirst_apply_succ_succ (A := 1) (B := B) (C := 0)
        (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
      simp [Matrix.one_apply, Fin.succ_inj]

omit [Finite F] in
private theorem mem_firstColRadical_of_blocks {C : Matrix (Fin (m+1)) (Fin 1) F}
    {x : SLm2 m F}
    (hx : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 C 1) :
    x ∈ firstColRadical m F := by
  rw [mem_colRadical]
  constructor
  · rw [hx]
    rw [fromBlocksFirst_apply_zero_zero (A := 1) (B := 0) (C := C)
      (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
    simp
  · intro i j hj
    rw [hx]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact absurd rfl hj
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [fromBlocksFirst_apply_zero_succ (A := 1) (B := 0) (C := C)
        (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
      rfl
    · rw [fromBlocksFirst_apply_succ_succ (A := 1) (B := 0) (C := C)
        (D := (1 : Matrix (Fin (m+1)) (Fin (m+1)) F))]
      simp [Matrix.one_apply, Fin.succ_inj]

omit [Finite F] in
private theorem mem_lastColRadical_of_blocks {B : Matrix (Fin (m+1)) (Fin 1) F}
    {x : SLm2 m F}
    (hx : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F 1 B 0 1) :
    x ∈ lastColRadical m F := by
  rw [mem_colRadical]
  constructor
  · rw [hx]
    rw [fromBlocksLast_apply_last_last (A := 1) (B := B) (C := 0)
      (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp
  · intro i j hj
    rw [hx]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
      · rw [fromBlocksLast_apply_castSucc_castSucc (A := 1) (B := B) (C := 0)
          (D := (1 : Matrix (Fin 1) (Fin 1) F))]
        simp [Matrix.one_apply]
      · rw [fromBlocksLast_apply_last_castSucc (A := 1) (B := B) (C := 0)
          (D := (1 : Matrix (Fin 1) (Fin 1) F)),
          Matrix.one_apply_ne (Fin.castSucc_ne_last j).symm]
        rfl
    · exfalso
      exact hj rfl

omit [Finite F] in
private theorem mem_lastRowRadical_of_blocks {C : Matrix (Fin 1) (Fin (m+1)) F}
    {x : SLm2 m F}
    (hx : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F 1 0 C 1) :
    x ∈ lastRowRadical m F := by
  rw [mem_rowRadical]
  constructor
  · rw [hx]
    rw [fromBlocksLast_apply_last_last (A := 1) (B := 0) (C := C)
      (D := (1 : Matrix (Fin 1) (Fin 1) F))]
    simp
  · intro i j hi
    rw [hx]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · rw [fromBlocksLast_apply_castSucc_castSucc (A := 1) (B := 0) (C := C)
          (D := (1 : Matrix (Fin 1) (Fin 1) F))]
        simp [Matrix.one_apply]
      · rw [fromBlocksLast_apply_castSucc_last (A := 1) (B := 0) (C := C)
          (D := (1 : Matrix (Fin 1) (Fin 1) F)),
          Matrix.one_apply_ne (Fin.castSucc_ne_last i)]
        rfl
    · exfalso
      exact hi rfl

omit [Finite F] in
theorem embedSucc_conj_mem_firstRow (a : SLm1 m F) {x : SLm2 m F}
    (hx : x ∈ firstRowRadical m F) :
    embedSucc m F a * x * (embedSucc m F a)⁻¹ ∈ firstRowRadical m F := by
  apply mem_firstRowRadical_of_blocks
  have hinv : (embedSucc m F a)⁻¹ = embedSucc m F a⁻¹ :=
    (map_inv (embedSucc m F) a).symm
  have hP : ((embedSucc m F a : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 0 ((a : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F) :=
    coe_embedSucc_eq_fromBlocksFirst m F a
  have hQ : (((embedSucc m F a)⁻¹ : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 0 (((a⁻¹ : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F)) := by
    rw [hinv]
    exact coe_embedSucc_eq_fromBlocksFirst m F a⁻¹
  have hX : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 (rowPart m F x) 0 1 :=
    coe_eq_fromBlocksFirst_of_mem_firstRow m F hx
  have hmat :
      ((embedSucc m F a * x * (embedSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksFirst m F 1
          (rowPart m F x * ((a⁻¹ : SLm1 m F) :
            Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 1 := by
    calc
      ((embedSucc m F a * x * (embedSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F)
          = ((embedSucc m F a : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (x : Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (((embedSucc m F a)⁻¹ : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
      _ = fromBlocksFirst m F 1
            (rowPart m F x * ((a⁻¹ : SLm1 m F) :
              Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 1 := by
        rw [hP, hX, hQ, fromBlocksFirst_mul, fromBlocksFirst_mul]
        simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
  exact hmat

omit [Finite F] in
theorem embedSucc_conj_mem_firstCol (a : SLm1 m F) {x : SLm2 m F}
    (hx : x ∈ firstColRadical m F) :
    embedSucc m F a * x * (embedSucc m F a)⁻¹ ∈ firstColRadical m F := by
  apply mem_firstColRadical_of_blocks
  have hinv : (embedSucc m F a)⁻¹ = embedSucc m F a⁻¹ :=
    (map_inv (embedSucc m F) a).symm
  have hP : ((embedSucc m F a : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 0 ((a : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F) :=
    coe_embedSucc_eq_fromBlocksFirst m F a
  have hQ : (((embedSucc m F a)⁻¹ : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 0 (((a⁻¹ : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F)) := by
    rw [hinv]
    exact coe_embedSucc_eq_fromBlocksFirst m F a⁻¹
  have hX : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksFirst m F 1 0 (colPart m F x) 1 :=
    coe_eq_fromBlocksFirst_of_mem_firstCol m F hx
  have hmat :
      ((embedSucc m F a * x * (embedSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksFirst m F 1 0
          ((a : Matrix (Fin (m+1)) (Fin (m+1)) F) * colPart m F x) 1 := by
    calc
      ((embedSucc m F a * x * (embedSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F)
          = ((embedSucc m F a : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (x : Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (((embedSucc m F a)⁻¹ : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
      _ = fromBlocksFirst m F 1 0
            ((a : Matrix (Fin (m+1)) (Fin (m+1)) F) * colPart m F x) 1 := by
        rw [hP, hX, hQ, fromBlocksFirst_mul, fromBlocksFirst_mul]
        simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
  exact hmat

omit [Finite F] in
theorem embedCastSucc_conj_mem_lastCol (a : SLm1 m F) {x : SLm2 m F}
    (hx : x ∈ lastColRadical m F) :
    embedCastSucc m F a * x * (embedCastSucc m F a)⁻¹ ∈ lastColRadical m F := by
  apply mem_lastColRadical_of_blocks
  have hinv : (embedCastSucc m F a)⁻¹ = embedCastSucc m F a⁻¹ :=
    (map_inv (embedCastSucc m F) a).symm
  have hP : ((embedCastSucc m F a : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F ((a : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F) 0 0 1 :=
    coe_embedCastSucc_eq_fromBlocksLast m F a
  have hQ : (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F (((a⁻¹ : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 0 1 := by
    rw [hinv]
    exact coe_embedCastSucc_eq_fromBlocksLast m F a⁻¹
  have hX : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F 1 (lastColPart m F x) 0 1 :=
    coe_eq_fromBlocksLast_of_mem_lastCol m F hx
  have hmat :
      ((embedCastSucc m F a * x * (embedCastSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksLast m F 1
          ((a : Matrix (Fin (m+1)) (Fin (m+1)) F) * lastColPart m F x) 0 1 := by
    calc
      ((embedCastSucc m F a * x * (embedCastSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F)
          = ((embedCastSucc m F a : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (x : Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
      _ = fromBlocksLast m F 1
            ((a : Matrix (Fin (m+1)) (Fin (m+1)) F) * lastColPart m F x) 0 1 := by
        rw [hP, hX, hQ, fromBlocksLast_mul, fromBlocksLast_mul]
        simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
  exact hmat

omit [Finite F] in
theorem embedCastSucc_conj_mem_lastRow (a : SLm1 m F) {x : SLm2 m F}
    (hx : x ∈ lastRowRadical m F) :
    embedCastSucc m F a * x * (embedCastSucc m F a)⁻¹ ∈ lastRowRadical m F := by
  apply mem_lastRowRadical_of_blocks
  have hinv : (embedCastSucc m F a)⁻¹ = embedCastSucc m F a⁻¹ :=
    (map_inv (embedCastSucc m F) a).symm
  have hP : ((embedCastSucc m F a : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F ((a : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F) 0 0 1 :=
    coe_embedCastSucc_eq_fromBlocksLast m F a
  have hQ : (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F (((a⁻¹ : SLm1 m F) :
        Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 0 1 := by
    rw [hinv]
    exact coe_embedCastSucc_eq_fromBlocksLast m F a⁻¹
  have hX : (x : Matrix (Fin (m+2)) (Fin (m+2)) F) =
      fromBlocksLast m F 1 0 (lastRowPart m F x) 1 :=
    coe_eq_fromBlocksLast_of_mem_lastRow m F hx
  have hmat :
      ((embedCastSucc m F a * x * (embedCastSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksLast m F 1 0
          (lastRowPart m F x * ((a⁻¹ : SLm1 m F) :
            Matrix (Fin (m+1)) (Fin (m+1)) F)) 1 := by
    calc
      ((embedCastSucc m F a * x * (embedCastSucc m F a)⁻¹ : SLm2 m F) :
          Matrix (Fin (m+2)) (Fin (m+2)) F)
          = ((embedCastSucc m F a : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (x : Matrix (Fin (m+2)) (Fin (m+2)) F) *
              (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
                Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
      _ = fromBlocksLast m F 1 0
            (lastRowPart m F x * ((a⁻¹ : SLm1 m F) :
              Matrix (Fin (m+1)) (Fin (m+1)) F)) 1 := by
        rw [hP, hX, hQ, fromBlocksLast_mul, fromBlocksLast_mul]
        simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
  exact hmat

omit [Fact (Nat.Prime p)] in
theorem embedSucc_mem_U {a : SLm1 m F} (ha : a ∈ (curtisDatum m F p).U) :
    embedSucc m F a ∈ (curtisDatum (m+1) F p).U := by
  have ha' := (mem_curtisDatum_U_iff (m := m) (F := F) (p := p)).mp ha
  rw [mem_curtisDatum_U_iff]
  constructor
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [coe_embedSucc_eq_fromBlocksFirst, fromBlocksFirst_apply_zero_zero]
      simp
    · rw [coe_embedSucc_eq_fromBlocksFirst, fromBlocksFirst_apply_succ_succ]
      exact ha'.1 i
  · intro i j hji
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · exfalso
      exact (not_le_of_gt hji) (Fin.zero_le j)
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rw [coe_embedSucc_eq_fromBlocksFirst, fromBlocksFirst_apply_succ_zero]
      rfl
    · rw [coe_embedSucc_eq_fromBlocksFirst, fromBlocksFirst_apply_succ_succ]
      exact ha'.2 i j (by simpa using hji)

omit [Fact (Nat.Prime p)] in
theorem embedCastSucc_mem_U {a : SLm1 m F} (ha : a ∈ (curtisDatum m F p).U) :
    embedCastSucc m F a ∈ (curtisDatum (m+1) F p).U := by
  have ha' := (mem_curtisDatum_U_iff (m := m) (F := F) (p := p)).mp ha
  rw [mem_curtisDatum_U_iff]
  constructor
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rw [coe_embedCastSucc_eq_fromBlocksLast,
        fromBlocksLast_apply_castSucc_castSucc]
      exact ha'.1 i
    · rw [coe_embedCastSucc_eq_fromBlocksLast, fromBlocksLast_apply_last_last]
      simp
  · intro i j hji
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · rw [coe_embedCastSucc_eq_fromBlocksLast,
          fromBlocksLast_apply_castSucc_castSucc]
        exact ha'.2 i j hji
      · exfalso
        exact (not_le_of_gt hji) (Fin.le_last i.castSucc)
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · rw [coe_embedCastSucc_eq_fromBlocksLast,
          fromBlocksLast_apply_last_castSucc]
        rfl
      · exfalso
        exact (not_le_of_gt hji) (le_refl _)

omit [Fact (Nat.Prime p)] in
theorem curtisDatum_U_le_firstRow_sup :
    (curtisDatum (m+1) F p).U ≤
      firstRowRadical m F ⊔
        ((curtisDatum (m+1) F p).U ⊓ (embedSucc m F).range) := by
  intro u hu
  let a : SLm1 m F :=
    ⟨bottomPartFirst m F u, det_bottomPartFirst_of_mem_U m F p hu⟩
  have haU : a ∈ (curtisDatum m F p).U := bottomPartFirst_mem_U m F p hu
  let p1 : SLm2 m F := embedSucc m F a
  have hp1U : p1 ∈ (curtisDatum (m+1) F p).U := embedSucc_mem_U m F p haU
  have hp1P : p1 ∈ (embedSucc m F).range := ⟨a, rfl⟩
  let n : SLm2 m F := u * p1⁻¹
  have hnN : n ∈ firstRowRadical m F := by
    apply mem_firstRowRadical_of_blocks
    have hQ : (((embedSucc m F a)⁻¹ : SLm2 m F) :
        Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksFirst m F 1 0 0 (((a⁻¹ : SLm1 m F) :
          Matrix (Fin (m+1)) (Fin (m+1)) F)) := by
      rw [(map_inv (embedSucc m F) a).symm]
      exact coe_embedSucc_eq_fromBlocksFirst m F a⁻¹
    have hmat :
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F) =
          fromBlocksFirst m F 1
            (rowPart m F u * ((a⁻¹ : SLm1 m F) :
              Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 1 := by
      calc
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F)
            = (u : Matrix (Fin (m+2)) (Fin (m+2)) F) *
                (((embedSucc m F a)⁻¹ : SLm2 m F) :
                  Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
        _ = fromBlocksFirst m F 1
              (rowPart m F u * ((a⁻¹ : SLm1 m F) :
                Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 1 := by
          rw [coe_eq_fromBlocksFirst_of_mem_U m F p hu, hQ,
            fromBlocksFirst_mul]
          rw [show bottomPartFirst m F u =
            (a : Matrix (Fin (m+1)) (Fin (m+1)) F) from rfl]
          simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
    exact hmat
  have hu_eq : u = n * p1 := by
    dsimp [n, p1]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hp1inf : p1 ∈ (curtisDatum (m+1) F p).U ⊓ (embedSucc m F).range :=
    ⟨hp1U, hp1P⟩
  have hmul : n * p1 ∈ firstRowRadical m F ⊔
      ((curtisDatum (m+1) F p).U ⊓ (embedSucc m F).range) :=
    Subgroup.mul_mem_sup hnN hp1inf
  rw [← hu_eq] at hmul
  exact hmul

omit [Fact (Nat.Prime p)] in
theorem curtisDatum_L_le_firstCol_sup :
    (curtisDatum (m+1) F p).L ≤
      firstColRadical m F ⊔ (embedSucc m F).range := by
  intro u hu
  let a : SLm1 m F :=
    ⟨bottomPartFirst m F u, det_bottomPartFirst_of_mem_L m F p hu⟩
  let p1 : SLm2 m F := embedSucc m F a
  have hp1P : p1 ∈ (embedSucc m F).range := ⟨a, rfl⟩
  let n : SLm2 m F := u * p1⁻¹
  have hnN : n ∈ firstColRadical m F := by
    apply mem_firstColRadical_of_blocks
    have hQ : (((embedSucc m F a)⁻¹ : SLm2 m F) :
        Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksFirst m F 1 0 0 (((a⁻¹ : SLm1 m F) :
          Matrix (Fin (m+1)) (Fin (m+1)) F)) := by
      rw [(map_inv (embedSucc m F) a).symm]
      exact coe_embedSucc_eq_fromBlocksFirst m F a⁻¹
    have hmat :
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F) =
          fromBlocksFirst m F 1 0 (colPart m F u) 1 := by
      calc
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F)
            = (u : Matrix (Fin (m+2)) (Fin (m+2)) F) *
                (((embedSucc m F a)⁻¹ : SLm2 m F) :
                  Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
        _ = fromBlocksFirst m F 1 0 (colPart m F u) 1 := by
          rw [coe_eq_fromBlocksFirst_of_mem_L m F p hu, hQ,
            fromBlocksFirst_mul]
          rw [show bottomPartFirst m F u =
            (a : Matrix (Fin (m+1)) (Fin (m+1)) F) from rfl]
          simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
    exact hmat
  have hu_eq : u = n * p1 := by
    dsimp [n, p1]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hmul : n * p1 ∈ firstColRadical m F ⊔ (embedSucc m F).range :=
    Subgroup.mul_mem_sup hnN hp1P
  rw [← hu_eq] at hmul
  exact hmul

omit [Fact (Nat.Prime p)] in
theorem curtisDatum_U_le_lastCol_sup :
    (curtisDatum (m+1) F p).U ≤
      lastColRadical m F ⊔
        ((curtisDatum (m+1) F p).U ⊓ (embedCastSucc m F).range) := by
  intro u hu
  let a : SLm1 m F :=
    ⟨bottomPartLast m F u, det_bottomPartLast_of_mem_U m F p hu⟩
  have haU : a ∈ (curtisDatum m F p).U := bottomPartLast_mem_U m F p hu
  let p1 : SLm2 m F := embedCastSucc m F a
  have hp1U : p1 ∈ (curtisDatum (m+1) F p).U := embedCastSucc_mem_U m F p haU
  have hp1P : p1 ∈ (embedCastSucc m F).range := ⟨a, rfl⟩
  let n : SLm2 m F := u * p1⁻¹
  have hnN : n ∈ lastColRadical m F := by
    apply mem_lastColRadical_of_blocks
    have hQ : (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
        Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksLast m F (((a⁻¹ : SLm1 m F) :
          Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 0 1 := by
      rw [(map_inv (embedCastSucc m F) a).symm]
      exact coe_embedCastSucc_eq_fromBlocksLast m F a⁻¹
    have hmat :
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F) =
          fromBlocksLast m F 1 (lastColPart m F u) 0 1 := by
      calc
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F)
            = (u : Matrix (Fin (m+2)) (Fin (m+2)) F) *
                (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
                  Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
        _ = fromBlocksLast m F 1 (lastColPart m F u) 0 1 := by
          rw [coe_eq_fromBlocksLast_of_mem_U m F p hu, hQ,
            fromBlocksLast_mul]
          rw [show bottomPartLast m F u =
            (a : Matrix (Fin (m+1)) (Fin (m+1)) F) from rfl]
          simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
    exact hmat
  have hu_eq : u = n * p1 := by
    dsimp [n, p1]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hp1inf : p1 ∈ (curtisDatum (m+1) F p).U ⊓ (embedCastSucc m F).range :=
    ⟨hp1U, hp1P⟩
  have hmul : n * p1 ∈ lastColRadical m F ⊔
      ((curtisDatum (m+1) F p).U ⊓ (embedCastSucc m F).range) :=
    Subgroup.mul_mem_sup hnN hp1inf
  rw [← hu_eq] at hmul
  exact hmul

omit [Fact (Nat.Prime p)] in
theorem curtisDatum_L_le_lastRow_sup :
    (curtisDatum (m+1) F p).L ≤
      lastRowRadical m F ⊔ (embedCastSucc m F).range := by
  intro u hu
  let a : SLm1 m F :=
    ⟨bottomPartLast m F u, det_bottomPartLast_of_mem_L m F p hu⟩
  let p1 : SLm2 m F := embedCastSucc m F a
  have hp1P' : p1 ∈ (embedCastSucc m F).range := ⟨a, rfl⟩
  let n : SLm2 m F := u * p1⁻¹
  have hnN : n ∈ lastRowRadical m F := by
    apply mem_lastRowRadical_of_blocks
    have hQ : (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
        Matrix (Fin (m+2)) (Fin (m+2)) F) =
        fromBlocksLast m F (((a⁻¹ : SLm1 m F) :
          Matrix (Fin (m+1)) (Fin (m+1)) F)) 0 0 1 := by
      rw [(map_inv (embedCastSucc m F) a).symm]
      exact coe_embedCastSucc_eq_fromBlocksLast m F a⁻¹
    have hmat :
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F) =
          fromBlocksLast m F 1 0
            (lastRowPart m F u * ((a⁻¹ : SLm1 m F) :
              Matrix (Fin (m+1)) (Fin (m+1)) F)) 1 := by
      calc
        (n : Matrix (Fin (m+2)) (Fin (m+2)) F)
            = (u : Matrix (Fin (m+2)) (Fin (m+2)) F) *
                (((embedCastSucc m F a)⁻¹ : SLm2 m F) :
                  Matrix (Fin (m+2)) (Fin (m+2)) F) := rfl
        _ = fromBlocksLast m F 1 0
              (lastRowPart m F u * ((a⁻¹ : SLm1 m F) :
                Matrix (Fin (m+1)) (Fin (m+1)) F)) 1 := by
          rw [coe_eq_fromBlocksLast_of_mem_L m F p hu, hQ,
            fromBlocksLast_mul]
          rw [show bottomPartLast m F u =
            (a : Matrix (Fin (m+1)) (Fin (m+1)) F) from rfl]
          simp [Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe]
    exact hmat
  have hu_eq : u = n * p1 := by
    dsimp [n, p1]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hmul : n * p1 ∈ lastRowRadical m F ⊔ (embedCastSucc m F).range :=
    Subgroup.mul_mem_sup hnN hp1P'
  rw [← hu_eq] at hmul
  exact hmul

omit [Finite F] in
theorem embedSucc_range_normalizes_firstRow :
    ∀ m' ∈ (embedSucc m F).range,
      ∀ x ∈ firstRowRadical m F, m' * x * m'⁻¹ ∈ firstRowRadical m F := by
  rintro m' ⟨a, rfl⟩ x hx
  exact embedSucc_conj_mem_firstRow m F a hx

omit [Finite F] in
theorem embedSucc_range_normalizes_firstCol :
    ∀ m' ∈ (embedSucc m F).range,
      ∀ x ∈ firstColRadical m F, m' * x * m'⁻¹ ∈ firstColRadical m F := by
  rintro m' ⟨a, rfl⟩ x hx
  exact embedSucc_conj_mem_firstCol m F a hx

omit [Finite F] in
theorem embedCastSucc_range_normalizes_lastCol :
    ∀ m' ∈ (embedCastSucc m F).range,
      ∀ x ∈ lastColRadical m F, m' * x * m'⁻¹ ∈ lastColRadical m F := by
  rintro m' ⟨a, rfl⟩ x hx
  exact embedCastSucc_conj_mem_lastCol m F a hx

omit [Finite F] in
theorem embedCastSucc_range_normalizes_lastRow :
    ∀ m' ∈ (embedCastSucc m F).range,
      ∀ x ∈ lastRowRadical m F, m' * x * m'⁻¹ ∈ lastRowRadical m F := by
  rintro m' ⟨a, rfl⟩ x hx
  exact embedCastSucc_conj_mem_lastRow m F a hx

end

end CFSG.LieType.SpecialLinear
