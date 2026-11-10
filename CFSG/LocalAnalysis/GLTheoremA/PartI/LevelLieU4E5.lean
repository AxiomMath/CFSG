module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3 σ4)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K card_K)
open Matrix

theorem zeta_ne_sq (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : ζ ≠ ζ ^ 2 := by
  intro h
  have hne1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hne0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have : ζ * (ζ - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hne0 h0
  · exact hne1 (sub_eq_zero.1 h0)

@[expose] def blkA (x : SU4) : Matrix (Fin 2) (Fin 2) K :=
  !![mat x 0 0, mat x 0 1; mat x 1 0, mat x 1 1]

theorem c022_zero {ζ : K} {hζ : IsPrimitiveRoot ζ 3} {x : SU4}
    (hx : x ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) :
    mat x 0 2 = 0 ∧ mat x 0 3 = 0 ∧ mat x 1 2 = 0 ∧ mat x 1 3 = 0 ∧
      mat x 2 0 = 0 ∧ mat x 2 1 = 0 ∧ mat x 3 0 = 0 ∧ mat x 3 1 = 0 := by
  have hd := mat_c022 ζ hζ
  have hne := zeta_ne_sq ζ hζ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact entry_zero_of_mem_centralizer hd hx (by simp [hne, hne.symm])

theorem blkA_mul {ζ : K} {hζ : IsPrimitiveRoot ζ 3} {x y : SU4}
    (hx : x ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4))
    (hy : y ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) :
    blkA (x * y) = blkA x * blkA y := by
  obtain ⟨x02, x03, x12, x13, x20, x21, x30, x31⟩ := c022_zero hx
  obtain ⟨y02, y03, y12, y13, y20, y21, y30, y31⟩ := c022_zero hy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkA, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, x02, x03, x12, x13, x20, x21,
      x30, x31, y02, y03, y12, y13, y20, y21, y30, y31]

theorem blkA_one : blkA 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkA, mat_one]

theorem blkA_unitary {ζ : K} {hζ : IsPrimitiveRoot ζ 3} {x : SU4}
    (hx : x ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) :
    LieType.Universal.Unitary.conjTr σ4 (blkA x) * blkA x = 1 := by
  obtain ⟨x02, x03, x12, x13, x20, x21, x30, x31⟩ := c022_zero hx
  have hU : LieType.Universal.Unitary.conjTr σ4 (mat x) * mat x = 1 :=
    (LieType.Universal.Unitary.mem_SUid.1 x.2).2
  have key : ∀ a b : Fin 4, (LieType.Universal.Unitary.conjTr σ4 (mat x) * mat x) a b =
      (1 : Matrix (Fin 4) (Fin 4) K) a b := fun a b => congrFun (congrFun hU a) b
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blkA, LieType.Universal.Unitary.conjTr, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_two, x02, x03, x12, x13, x20, x21, x30, x31] using key 0 0
  · simpa [blkA, LieType.Universal.Unitary.conjTr, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_two, x02, x03, x12, x13, x20, x21, x30, x31] using key 0 1
  · simpa [blkA, LieType.Universal.Unitary.conjTr, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_two, x02, x03, x12, x13, x20, x21, x30, x31] using key 1 0
  · simpa [blkA, LieType.Universal.Unitary.conjTr, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_two, x02, x03, x12, x13, x20, x21, x30, x31] using key 1 1

theorem blkA_det_ne {ζ : K} {hζ : IsPrimitiveRoot ζ 3} {x : SU4}
    (hx : x ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) : (blkA x).det ≠ 0 := by
  have hi : x⁻¹ ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) := Subgroup.inv_mem _ hx
  have h : blkA x⁻¹ * blkA x = 1 := by
    rw [← blkA_mul hi hx, inv_mul_cancel, blkA_one]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact right_ne_zero_of_mul_eq_one h2

@[expose] def KA (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : Subgroup SU4 where
  carrier := {x | x ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) ∧ (blkA x).det = 1}
  mul_mem' := by
    rintro x y ⟨hx, hdx⟩ ⟨hy, hdy⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    rw [blkA_mul hx hy, Matrix.det_mul, hdx, hdy, one_mul]
  one_mem' := ⟨Subgroup.one_mem _, by rw [blkA_one, Matrix.det_one]⟩
  inv_mem' := by
    rintro x ⟨hx, hdx⟩
    refine ⟨Subgroup.inv_mem _ hx, ?_⟩
    have hi : x⁻¹ ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) := Subgroup.inv_mem _ hx
    have h : blkA x⁻¹ * blkA x = 1 := by
      rw [← blkA_mul hi hx, inv_mul_cancel, blkA_one]
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one, hdx, mul_one] at h2
    exact h2

open CFSG.ClassicalInvolution.Phan (Su blockEmb blockEmb_injective mem_range_blockEmb_iff)

@[expose] noncomputable def blkSu (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (x : SU4)
    (hx : x ∈ KA ζ hζ) : Su K 2 3 2 :=
  ⟨Units.mk (blkA x) (LieType.Universal.Unitary.conjTr σ4 (blkA x))
    (mul_eq_one_comm.1 (blkA_unitary hx.1)) (blkA_unitary hx.1),
    LieType.Universal.Unitary.mem_SUid.2 ⟨hx.2, blkA_unitary hx.1⟩⟩

theorem coe_blkSu (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (x : SU4) (hx : x ∈ KA ζ hζ) :
    (((blkSu ζ hζ x hx : Su K 2 3 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = blkA x :=
  rfl

@[expose] noncomputable def thetaA (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : KA ζ hζ →* Su K 2 3 2 where
  toFun x := blkSu ζ hζ x x.2
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    show blkA ((1 : KA ζ hζ) : SU4) = 1
    exact blkA_one
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact blkA_mul x.2.1 y.2.1

theorem blkA_blockEmb (a : Su K 2 3 2) :
    blkA (blockEmb K 2 3 4 2 0 (by norm_num) a : SU4) =
      ((a : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkA, mat, CFSG.ClassicalInvolution.Phan.coe_coe_blockEmb, CFSG.ClassicalInvolution.Phan.blockMat_apply]

@[expose] noncomputable def piA (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : KA ζ hζ →* SU4 :=
  (blockEmb K 2 3 4 2 0 (by norm_num)).comp (thetaA ζ hζ)

theorem piA_mem_W0 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) (x : KA ζ hζ) : piA ζ hζ x ∈ W0 :=
  ⟨thetaA ζ hζ x, rfl⟩

theorem col_of_fix (x : SU4) (i k : Fin 4) (hx : x • (Pi.single i 1 : Fin 4 → K) = Pi.single i 1) :
    mat x k i = if k = i then 1 else 0 := by
  have := congrFun hx k
  rw [smul_single_eq] at this
  rw [this, Pi.single_apply]

noncomputable abbrev W1 : Subgroup SU4 := (blockEmb K 2 3 4 2 2 (by norm_num)).range

theorem mem_W1_iff (g : SU4) :
    g ∈ W1 ↔ g • (Pi.single 0 1 : Fin 4 → K) = Pi.single 0 1 ∧
      g • (Pi.single 1 1 : Fin 4 → K) = Pi.single 1 1 := by
  rw [mem_range_blockEmb_iff]
  constructor
  · intro h
    exact ⟨h 0 (by simp), h 1 (by simp)⟩
  · rintro ⟨h0, h1⟩ l hl
    have hl2 : l = 0 ∨ l = 1 := by
      have := l.isLt
      by_cases h' : l.val < 2
      · rcases (show l.val = 0 ∨ l.val = 1 by omega) with h'' | h''
        · left; exact Fin.ext h''
        · right; exact Fin.ext h''
      · exact (hl ⟨by omega, by omega⟩).elim
    rcases hl2 with rfl | rfl
    · exact h0
    · exact h1

theorem W1_entry (x : SU4) (h0 : x • (Pi.single 0 1 : Fin 4 → K) = Pi.single 0 1)
    (h1 : x • (Pi.single 1 1 : Fin 4 → K) = Pi.single 1 1) (i j : Fin 4)
    (hij : i = 0 ∨ i = 1 ∨ j = 0 ∨ j = 1) : mat x i j = if i = j then 1 else 0 := by
  rcases hij with rfl | rfl | rfl | rfl
  · rw [row_of_fix x 0 h0 j]
  · rw [row_of_fix x 1 h1 j]
  · rw [col_of_fix x 0 i h0]
  · rw [col_of_fix x 1 i h1]

theorem mem_centralizer_of_zero {c : SU4} {d : Fin 4 → K} (hc : mat c = diagonal d) {x : SU4}
    (hz : ∀ i j, d i ≠ d j → mat x i j = 0) : x ∈ Subgroup.centralizer ({c} : Set SU4) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mat_eq_of_mat_eq
  rw [mat_mul, mat_mul, hc]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : d i = d j
  · rw [hij, mul_comm]
  · rw [hz i j hij]
    simp

theorem W1_le_centralizer_c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    W1 ≤ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) := by
  intro x hx
  obtain ⟨h0, h1⟩ := (mem_W1_iff x).1 hx
  have hne := zeta_ne_sq ζ hζ
  refine mem_centralizer_of_zero (mat_c022 ζ hζ) (fun i j hij => ?_)
  have hcase : i = 0 ∨ i = 1 ∨ j = 0 ∨ j = 1 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rw [W1_entry x h0 h1 i j hcase, if_neg]
  rintro rfl
  exact hij rfl

theorem W0_le_centralizer_c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    W0 ≤ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) := by
  intro x hx
  obtain ⟨h2, h3⟩ := (mem_W0_iff x).1 hx
  have hne := zeta_ne_sq ζ hζ
  refine mem_centralizer_of_zero (mat_c022 ζ hζ) (fun i j hij => ?_)
  have hcase : i = 2 ∨ i = 3 ∨ j = 2 ∨ j = 3 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rw [W0_entry x h2 h3 i j hcase, if_neg]
  rintro rfl
  exact hij rfl

theorem W1_normal_c022 {ζ : K} {hζ : IsPrimitiveRoot ζ 3} {g : SU4}
    (hg : g ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) {n : SU4} (hn : n ∈ W1) :
    g * n * g⁻¹ ∈ W1 := by
  obtain ⟨hn0, hn1⟩ := (mem_W1_iff n).1 hn
  have hgi : g⁻¹ ∈ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) := Subgroup.inv_mem _ hg
  obtain ⟨-, -, -, -, g20, g21, g30, g31⟩ := c022_zero hgi
  have c0 : ∀ k, mat n k 0 = if k = 0 then 1 else 0 := fun k => col_of_fix n 0 k hn0
  have c1 : ∀ k, mat n k 1 = if k = 1 then 1 else 0 := fun k => col_of_fix n 1 k hn1
  have fix0 : n • (g⁻¹ • (Pi.single 0 1 : Fin 4 → K)) = g⁻¹ • (Pi.single 0 1 : Fin 4 → K) := by
    funext k
    fin_cases k <;>
      simp [smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_four, smul_single_eq, c0, c1,
        g20, g21, g30, g31]
  have fix1 : n • (g⁻¹ • (Pi.single 1 1 : Fin 4 → K)) = g⁻¹ • (Pi.single 1 1 : Fin 4 → K) := by
    funext k
    fin_cases k <;>
      simp [smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_four, smul_single_eq, c0, c1,
        g20, g21, g30, g31]
  rw [mem_W1_iff]
  constructor
  · rw [mul_smul, mul_smul, fix0, smul_inv_smul]
  · rw [mul_smul, mul_smul, fix1, smul_inv_smul]

theorem piA_ker {ζ : K} {hζ : IsPrimitiveRoot ζ 3} (y : KA ζ hζ) (hy : piA ζ hζ y = 1) :
    (y : SU4) ∈ W1 := by
  have h1 : thetaA ζ hζ y = 1 := by
    apply (blockEmb_injective (K := K) (p := 2) (f := 3) (by norm_num : 0 + 2 ≤ 4))
    rw [map_one]
    exact hy
  have hb : blkA (y : SU4) = 1 := by
    rw [← coe_blkSu ζ hζ (y : SU4) y.2]
    have h2 : ((thetaA ζ hζ y : Su K 2 3 2) : GL (Fin 2) K) = 1 := by
      rw [h1]; rfl
    rw [show (((blkSu ζ hζ (y : SU4) y.2 : Su K 2 3 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (((thetaA ζ hζ y : Su K 2 3 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) from rfl, h2]
    simp
  have e00 := congrFun (congrFun hb 0) 0
  have e01 := congrFun (congrFun hb 0) 1
  have e10 := congrFun (congrFun hb 1) 0
  have e11 := congrFun (congrFun hb 1) 1
  obtain ⟨-, -, -, -, g20, g21, g30, g31⟩ := c022_zero y.2.1
  simp only [blkA, Matrix.of_apply, Matrix.cons_val, Matrix.one_apply] at e00 e01 e10 e11
  rw [mem_W1_iff]
  constructor
  · funext k
    rw [smul_single_eq, Pi.single_apply]
    fin_cases k <;> simp_all
  · funext k
    rw [smul_single_eq, Pi.single_apply]
    fin_cases k <;> simp_all

theorem W0_le_KA {ζ : K} {hζ : IsPrimitiveRoot ζ 3} {w : SU4} (hw : w ∈ W0) : w ∈ KA ζ hζ := by
  obtain ⟨a, rfl⟩ := hw
  refine ⟨W0_le_centralizer_c022 ζ hζ ⟨a, rfl⟩, ?_⟩
  rw [blkA_blockEmb]
  exact (LieType.Universal.Unitary.mem_SUid.1 a.2).1

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
