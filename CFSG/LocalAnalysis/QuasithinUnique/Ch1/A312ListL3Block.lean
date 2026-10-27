module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Entries

variable {n : ℕ} {K : Type*} [Field K]

theorem mem_stabilizer_of_entries {i : ℕ} {g : SpecialLinearGroup (Fin n) K}
    (h : ∀ k l : Fin n, i ≤ (k : ℕ) → (l : ℕ) < i → (g : Matrix (Fin n) (Fin n) K) k l = 0) :
    g ∈ stabilizer (flagSpace n K i) := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v ∈ flagSpace n K i := hv
  rw [mulVecLin_apply, mem_flagSpace]
  intro k hk
  rw [mem_flagSpace] at hv'
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < i
  · rw [h k l hk hl, zero_mul]
  · rw [hv' l (not_lt.mp hl), mul_zero]

end Entries

section Three

variable {K : Type*} [Field K]

@[expose] def embMat (j : Fin 2) (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  if j = 0 then !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]
  else !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem det_embMat (j : Fin 2) {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    (embMat j A).det = 1 := by
  rw [Matrix.det_fin_two] at hA
  fin_cases j
  · simp only [embMat, Fin.zero_eta, Fin.isValue, ite_true, Matrix.det_fin_three]
    simp
    linear_combination hA
  · simp only [embMat, Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, Matrix.det_fin_three]
    simp
    linear_combination hA

theorem embMat_one (j : Fin 2) : embMat j (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext r l
  fin_cases j <;> fin_cases r <;> fin_cases l <;> simp [embMat]

theorem embMat_mul (j : Fin 2) (A B : Matrix (Fin 2) (Fin 2) K) :
    embMat j (A * B) = embMat j A * embMat j B := by
  ext r l
  fin_cases j <;> fin_cases r <;> fin_cases l <;>
    simp [embMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

@[expose] noncomputable def embSL (j : Fin 2) :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨embMat j A, det_embMat j A.2⟩
  map_one' := Subtype.ext (embMat_one j)
  map_mul' A B := Subtype.ext (embMat_mul j A.1 B.1)

theorem coe_embSL (j : Fin 2) (A : SpecialLinearGroup (Fin 2) K) :
    ((embSL j A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = embMat j A := rfl

theorem embSL_mem_Q3 (j : Fin 2) (A : SpecialLinearGroup (Fin 2) K) : embSL j A ∈ Q3 K j := by
  show embSL j A ∈ stabilizer (flagSpace 3 K ((j : ℕ) + 1))
  refine mem_stabilizer_of_entries fun k l hk hl => ?_
  rw [coe_embSL]
  fin_cases j <;> fin_cases k <;> fin_cases l <;> simp [embMat] at hk hl ⊢

theorem q3_blockLeft (j : Fin 2) : BlockLeft (Q3 K j) (1 - (j : ℕ)) 2 := by
  fin_cases j
  · exact blockLeft_of_stabilizer fun g hg => hg
  · exact blockLeft_zero _ _

theorem q3_blockRight (j : Fin 2) : BlockRight (Q3 K j) (1 - (j : ℕ)) 2 := by
  fin_cases j
  · exact blockRight_top _ (by norm_num)
  · exact blockRight_of_stabilizer fun g hg => hg

theorem q3_blk_le (j : Fin 2) : 1 - (j : ℕ) + 2 ≤ 3 := by omega

theorem blkAt_embMat (j : Fin 2) (A : Matrix (Fin 2) (Fin 2) K) :
    blkAt (1 - (j : ℕ)) 2 (q3_blk_le j) (embMat j A) = A := by
  ext i k
  fin_cases j <;> fin_cases i <;> fin_cases k <;> simp [blkAt, embMat]

theorem embSL_range_perfect (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    ⁅(embSL (K := K) j).range, (embSL (K := K) j).range⁆ = (embSL (K := K) j).range := by
  have h : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Group.isPerfect_def.mp (CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK)
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

section Finite

variable [Finite K]

theorem perfect_perfectCore_Q3 (j : Fin 2) : Group.IsPerfect ↥(perfectCore (Q3 K j)) :=
  Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)

@[expose] noncomputable def blk3 (j : Fin 2) : ↥(perfectCore (Q3 K j)) →* SpecialLinearGroup (Fin 2) K :=
  blkSL (Q3 K j) (1 - (j : ℕ)) 2 (q3_blk_le j) (q3_blockLeft j) (q3_blockRight j)
    (perfectCore_le (Q3 K j)) (perfect_perfectCore_Q3 j)

theorem blk3_coe (j : Fin 2) (x : ↥(perfectCore (Q3 K j))) :
    ((blk3 j x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blkAt (1 - (j : ℕ)) 2 (q3_blk_le j) (x.1 : Matrix (Fin 3) (Fin 3) K) := rfl

omit [Finite K] in
theorem embSL_mem_perfectCore (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2)
    (A : SpecialLinearGroup (Fin 2) K) : embSL j A ∈ perfectCore (Q3 K j) :=
  le_perfectCore_of_perfect (K := (embSL (K := K) j).range) (H := Q3 K j)
    (by rintro _ ⟨B, rfl⟩; exact embSL_mem_Q3 j B) (embSL_range_perfect hK j) ⟨A, rfl⟩

theorem blk3_embSL (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2)
    (A : SpecialLinearGroup (Fin 2) K) :
    blk3 j ⟨embSL j A, embSL_mem_perfectCore hK j A⟩ = A :=
  Subtype.ext (blkAt_embMat j A.1)

theorem blk3_surjective (hK : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    Function.Surjective (blk3 (K := K) j) :=
  fun A => ⟨⟨embSL j A, embSL_mem_perfectCore hK j A⟩, blk3_embSL hK j A⟩

end Finite

theorem mem_unitriangular_three {x : SpecialLinearGroup (Fin 3) K}
    (h10 : (x : Matrix (Fin 3) (Fin 3) K) 1 0 = 0) (h20 : (x : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (x : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) (h00 : (x : Matrix (Fin 3) (Fin 3) K) 0 0 = 1)
    (h11 : (x : Matrix (Fin 3) (Fin 3) K) 1 1 = 1) (h22 : (x : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    x ∈ unitriangular 3 K := by
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases k <;>
      first | exact absurd hik (by decide) | exact h10 | exact h20 | exact h21
  · fin_cases i <;> first | exact h00 | exact h11 | exact h22

theorem blk3_ker_aux (j : Fin 2) (x : SpecialLinearGroup (Fin 3) K) (hxQ : x ∈ Q3 K j)
    (hb : ∀ i k : Fin 2, blkAt (1 - (j : ℕ)) 2 (q3_blk_le j) (x : Matrix (Fin 3) (Fin 3) K) i k =
      (1 : Matrix (Fin 2) (Fin 2) K) i k) : x ∈ unitriangular 3 K := by
  have hdet := x.2
  rw [Matrix.det_fin_three] at hdet
  fin_cases j
  · have hxQ' : x ∈ stabilizer (flagSpace 3 K 1) := hxQ
    have h10 := stabilizer_entries (k := 1) (l := 0) hxQ' (by norm_num) (by norm_num)
    have h20 := stabilizer_entries (k := 2) (l := 0) hxQ' (by norm_num) (by norm_num)
    have e11 := hb 0 0
    have e12 := hb 0 1
    have e21 := hb 1 0
    have e22 := hb 1 1
    simp [blkAt] at e11 e12 e21 e22
    rw [e11, e12, e21, e22, h10, h20] at hdet
    refine mem_unitriangular_three h10 h20 e21 ?_ e11 e22
    simpa using hdet
  · have hxQ' : x ∈ stabilizer (flagSpace 3 K 2) := hxQ
    have h20 := stabilizer_entries (k := 2) (l := 0) hxQ' (by norm_num) (by norm_num)
    have h21 := stabilizer_entries (k := 2) (l := 1) hxQ' (by norm_num) (by norm_num)
    have e00 := hb 0 0
    have e01 := hb 0 1
    have e10 := hb 1 0
    have e11 := hb 1 1
    simp [blkAt] at e00 e01 e10 e11
    rw [e00, e01, e10, e11, h20, h21] at hdet
    refine mem_unitriangular_three e10 h20 h21 e00 e11 ?_
    simpa using hdet

section FiniteKer

variable [Finite K]

theorem blk3_ker (j : Fin 2) (x : ↥(perfectCore (Q3 K j))) (hx : blk3 j x = 1) :
    (x : SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K := by
  refine blk3_ker_aux j _ (perfectCore_le _ x.2) fun i k => ?_
  have := congrArg (fun y : SpecialLinearGroup (Fin 2) K => (y : Matrix (Fin 2) (Fin 2) K) i k) hx
  exact this

theorem blk3_scalars [CharP K 2] (j : Fin 2) (x : ↥(perfectCore (Q3 K j)))
    (hx : (x : SpecialLinearGroup (Fin 3) K) ∈ scalars 3 K) : x = 1 := by
  obtain ⟨c, -, hxc⟩ := hx
  have hdet := (blk3 j x).2
  rw [blk3_coe] at hdet
  have hblk : blkAt (1 - (j : ℕ)) 2 (q3_blk_le j) (x.1 : Matrix (Fin 3) (Fin 3) K) =
      scalar (Fin 2) (c : K) := by
    ext i k
    rw [blkAt_apply, hxc]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Fin.ext_iff]
  rw [hblk, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc1 : (c : K) = 1 := CharTwo.sq_injective (by
    show (c : K) ^ 2 = 1 ^ 2
    rw [one_pow]
    exact hdet)
  refine Subtype.ext (Subtype.ext ?_)
  show (x.1 : Matrix (Fin 3) (Fin 3) K) = (1 : Matrix (Fin 3) (Fin 3) K)
  rw [hxc, hc1, map_one]

end FiniteKer

end Three

end CFSG.QuasithinUnique.Vol2Native.A312L
