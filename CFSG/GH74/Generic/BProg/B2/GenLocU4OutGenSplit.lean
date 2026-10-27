module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutGenBase
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutNF

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace GenLocU4Out

open GenLocU4Basic

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def rot02 : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1]

theorem rot02_det : (rot02 : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [rot02, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem rot02_map (hq : Odd (p ^ f)) : (rot02 : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) = rot02 := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot02, zero_pow hq0, Odd.neg_pow hq]

theorem rot02_unitary (hq : Odd (p ^ f)) : IsUnitaryU (p ^ f) (rot02 : Matrix (Fin 4) (Fin 4) K) := by
  unfold IsUnitaryU
  rw [rot02_map hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot02, Matrix.mul_apply, Fin.sum_univ_four]

theorem rot02_fixOut (δ : K) (hq : Odd (p ^ f)) :
    FixOut (p ^ f) (Matrix.diagonal ![1, 1, 1, δ] : Matrix (Fin 4) (Fin 4) K)
      (suOf (p ^ f) rot02 (rot02_unitary hq) rot02_det) := by
  unfold FixOut
  rw [coe_suOf, rot02_map hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot02, Matrix.mul_apply, Matrix.diagonal]

@[expose] def tvB (q : ℕ) (c ξ : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1 + c, c * ξ ^ q; c * ξ, 1 + c * (ξ * ξ ^ q)]

theorem tvB_det {q : ℕ} {c ξ : K} (hξ : ξ ^ q * ξ = -1) : (tvB q c ξ).det = 1 := by
  rw [tvB, Matrix.det_fin_two_of]
  linear_combination c * hξ

theorem tvB_unitary [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) {c ξ : K}
    (hc : c + c ^ (p ^ f) = 0) (hξ : ξ ^ (p ^ f) * ξ = -1) :
    ((tvB (p ^ f) c ξ).map (· ^ (p ^ f)))ᵀ * tvB (p ^ f) c ξ = 1 := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hb : ∀ x : K, x ^ (p ^ f) = h.bar x := fun x => (h.bar_apply x).symm
  have hbb : ∀ x : K, h.bar (h.bar x) = x := h.bar_bar
  simp only [hb] at hc hξ
  have hc' : h.bar c = -c := by linear_combination hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tvB, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, hb, hc', hbb] <;>
    first
    | linear_combination (-c ^ 2) * hξ
    | linear_combination (-c ^ 2 * h.bar ξ) * hξ
    | linear_combination (-c ^ 2 * ξ) * hξ
    | linear_combination (-c ^ 2 * (ξ * h.bar ξ)) * hξ

theorem tv_matrix (hq0 : p ^ f ≠ 0) (c ξ : K) :
    (1 + c • Matrix.vecMulVec (![1, 0, 0, ξ] : Fin 4 → K) (fun i => (![1, 0, 0, ξ] : Fin 4 → K) i ^ (p ^ f)) :
      Matrix (Fin 4) (Fin 4) K) =
    !![1 + c, 0, 0, c * ξ ^ (p ^ f); 0, 1, 0, 0; 0, 0, 1, 0; c * ξ, 0, 0, 1 + c * (ξ * ξ ^ (p ^ f))] := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [zero_pow hq0]

theorem conj_tv_block (hq : Odd (p ^ f)) (c ξ : K) :
    ((rot02 : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      (1 + c • Matrix.vecMulVec (![1, 0, 0, ξ] : Fin 4 → K) (fun i => (![1, 0, 0, ξ] : Fin 4 → K) i ^ (p ^ f))) *
        rot02 = CFSG.ClassicalInvolution.Phan.blockMat 4 2 (tvB (p ^ f) c ξ) := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  rw [rot02_map hq, tv_matrix hq0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot02, tvB, CFSG.ClassicalInvolution.Phan.blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four]

theorem transv_mem_of_rot [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) (hq : Odd (p ^ f))
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (δ : K)
    (hSO : ∀ g, FixOut (p ^ f) (Matrix.diagonal ![1, 1, 1, δ] : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (hB2 : ∀ g, GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 2 g → g ∈ Γ)
    {ξ : K} (hξ : ξ ^ (p ^ f) * ξ = -1) :
    ∀ g : ↥(StatedSU 4 (p ^ f) K), GenLocU4Gen.IsTransvU (p ^ f)
      (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ ![1, 0, 0, ξ]) g → g ∈ Γ := by
  rintro g ⟨c, hc, hc0, hg⟩
  have hw : ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (![1, 0, 0, ξ] : Fin 4 → K) = ![1, 0, 0, ξ] := by
    simp
  rw [hw] at hg
  let rG : ↥(StatedSU 4 (p ^ f) K) := suOf (p ^ f) rot02 (rot02_unitary hq) rot02_det
  have hrΓ : rG ∈ Γ := hSO _ (rot02_fixOut δ hq)
  have hinv : (((rG : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((rot02 : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ :=
    coe_inv_suOf (p ^ f) rot02 (rot02_unitary hq) rot02_det
  have hg' : GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 2 (rG⁻¹ * g * rG) := by
    refine ⟨tvB (p ^ f) c ξ, tvB_det hξ, tvB_unitary hp hK hc hξ, ?_⟩
    simp only [inv_one, one_mul, mul_one, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hinv, hg]
    exact conj_tv_block hq c ξ
  have h1 : rG⁻¹ * g * rG ∈ Γ := hB2 _ hg'
  have h2 : g = rG * (rG⁻¹ * g * rG) * rG⁻¹ := by group
  rw [h2]
  exact Γ.mul_mem (Γ.mul_mem hrΓ h1) (Γ.inv_mem hrΓ)

theorem tT_const (i : ℕ) (hi : i = 0 ∨ i = 2) :
    ∀ a b : Fin 4, (i ≤ a.val ∧ a.val < i + 2) → (i ≤ b.val ∧ b.val < i + 2) →
      (![1, 1, -1, -1] : Fin 4 → K) a = (![1, 1, -1, -1] : Fin 4 → K) b := by
  intro a b ha hb
  rcases hi with rfl | rfl <;> fin_cases a <;> fin_cases b <;> simp_all

theorem eq_top_of_blocks_rot [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (δ : K)
    (hSO : ∀ g, FixOut (p ^ f) (Matrix.diagonal ![1, 1, 1, δ] : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ)
    (hB0 : ∀ g, GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 0 g → g ∈ Γ)
    (hB2 : ∀ g, GenLocU4Gen.InBlock (p ^ f) (1 : GL (Fin 4) K) 2 g → g ∈ Γ) : Γ = ⊤ := by
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  obtain ⟨ξ, hξ⟩ := exists_norm_neg_one hp hK
  have hP1 : (((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    simp [Matrix.map_one, zero_pow hq0]
  refine GenLocU4Gen.su4_eq_top_of_link_raw hp hp2 hK Γ 1 hP1 hB0 hB2 ![1, 0, 0, ξ] ?_ ?_
    (transv_mem_of_rot hp hK hq Γ δ hSO hB2 hξ)
  · simp [Fin.sum_univ_four, zero_pow hq0, hξ]
  · simp [zero_pow hq0]

theorem outSplitGen (K : Type) [Field K] [Finite K] (p f : ℕ) : OutSplitGen K p f := by
  intro hp hp2 hK _ Γ hSO hT _
  exact eq_top_of_blocks_rot hp hp2 hK Γ (-1) hSO
    (fun g hg => hT g (commute_diag_of_block 0 _ (tT_const 0 (Or.inl rfl)) g hg))
    (fun g hg => hT g (commute_diag_of_block 2 _ (tT_const 2 (Or.inr rfl)) g hg))

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
