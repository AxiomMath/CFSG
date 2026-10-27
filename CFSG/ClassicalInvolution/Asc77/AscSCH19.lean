module

public import CFSG.ClassicalInvolution.Asc77.AscSCH18
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

theorem card_statedSU_four {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) :
    Nat.card (StatedSU 4 (ℓ ^ f) K) =
      (ℓ ^ f) ^ 6 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) * ((ℓ ^ f) ^ 4 - 1) := by
  have := h.finite
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 4) (Fin 4) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) (by norm_num)).2.1
  have h1 : (Nat.card (StatedSU 4 (ℓ ^ f) K) : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ (4 * (4 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 4, (((ℓ ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [show StatedSU 4 (ℓ ^ f) K = unitarySU ℓ f K 4 from rfl, unitarySU_eq_gramSU h,
      card_gramSU, hU]
  have hq : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have e2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have e4 : 1 ≤ (ℓ ^ f) ^ 4 := Nat.one_le_pow _ _ hq
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((ℓ ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 3 + 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 4 - 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3)]
    simp
  rw [hprod] at h1
  zify [e2, e4]
  rw [h1]
  norm_num
  ring

section SUmem

variable {q : ℕ}

theorem mem_statedSU_of_fixed (x : GL (Fin 4) K)
    (hdet : (x : Matrix (Fin 4) (Fin 4) K).det = 1)
    (hfix : (x : Matrix (Fin 4) (Fin 4) K).map (· ^ q) = x)
    (horth : (x : Matrix (Fin 4) (Fin 4) K)ᵀ * x = 1) : x ∈ StatedSU 4 q K :=
  Subgroup.subset_closure ⟨hdet, by rw [hfix]; exact horth⟩

theorem diagHom_mem_statedSU (hq : q ≠ 0) (d : Fin 4 → Kˣ)
    (hd : ∀ i, ((d i : Kˣ) : K) ^ (q + 1) = 1) (hdet : ∏ i, ((d i : Kˣ) : K) = 1) :
    diagHom 4 d ∈ StatedSU 4 q K := by
  refine Subgroup.subset_closure ⟨by rw [det_diagHom]; exact hdet, ?_⟩
  rw [coe_diagHom, Matrix.diagonal_map (by simp [hq]), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← pow_succ]
  exact hd i

theorem cyc4GL_mem_statedSU (hq : q ≠ 0) : (cyc4GL : GL (Fin 4) K) ∈ StatedSU 4 q K := by
  refine mem_statedSU_of_fixed _ det_cyc4GL ?_ cyc4Mat_transpose_mul
  rw [coe_cyc4GL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc4Mat, hq]

theorem w02GL_mem_statedSU (hq : q ≠ 0) (hodd : Odd q) :
    (w02GL : GL (Fin 4) K) ∈ StatedSU 4 q K := by
  refine mem_statedSU_of_fixed _ det_w02GL ?_ ?_
  · rw [coe_w02GL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w02Mat, hq, hodd.neg_one_pow]
  · rw [coe_w02GL]
    have : (w02Mat (K := K))ᵀ = w02Mat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w02Mat]
    rw [this]
    exact w02Mat_mul_self

theorem w13GL_mem_statedSU (hq : q ≠ 0) (hodd : Odd q) :
    (w13GL : GL (Fin 4) K) ∈ StatedSU 4 q K := by
  refine mem_statedSU_of_fixed _ det_w13GL ?_ ?_
  · rw [coe_w13GL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w13Mat, hq, hodd.neg_one_pow]
  · rw [coe_w13GL]
    have : (w13Mat (K := K))ᵀ = w13Mat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w13Mat]
    rw [this]
    exact w13Mat_mul_self

theorem w01GL_mem_statedSU (hq : q ≠ 0) (hodd : Odd q) :
    (w01GL : GL (Fin 4) K) ∈ StatedSU 4 q K := by
  refine mem_statedSU_of_fixed _ det_w01GL ?_ ?_
  · rw [coe_w01GL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w01Mat, hq, hodd.neg_one_pow]
  · rw [coe_w01GL]
    have : (w01Mat (K := K))ᵀ = w01Mat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [w01Mat]
    rw [this]
    exact w01Mat_mul_self

end SUmem

theorem statedSU_four_perfect_ker_eq_bot_two {ℓ f : ℕ} (hℓ2 : ℓ ≠ 2)
    (h : UnitaryFieldData ℓ f K) (h3 : 3 ∣ ℓ ^ f + 1) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (π : E →* StatedSU 4 (ℓ ^ f) K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  have := h.finite
  have hℓ := h.prime
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ hℓ.ne_zero
  have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq2 : 2 ≤ ℓ ^ f := by
    have hf1 := h.one_le
    have := Nat.one_lt_pow (n := f) (by omega) hℓ.one_lt
    omega
  obtain ⟨m, hm⟩ := IsCyclic.exists_generator (α := normOne K (ℓ ^ f))
  have hord : orderOf (m : Kˣ) = ℓ ^ f + 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hm,
      card_normOne (by rw [h.card, pow_mul'])]
  have hmn : ((m : Kˣ) : K) ^ (ℓ ^ f + 1) = 1 := by
    have := mem_normOne.1 m.2
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  refine ker_eq_bot_of_monomial_torus (m : Kˣ) (StatedSU 4 (ℓ ^ f) K) ?_ ?_ ?_
    (cyc4GL_mem_statedSU hq0) (w02GL_mem_statedSU hq0 hodd) (w13GL_mem_statedSU hq0 hodd)
    (w01GL_mem_statedSU hq0 hodd) ?_ π hπ hC hCp
  · refine diagHom_mem_statedSU hq0 _ (fun i => ?_) ?_
    · fin_cases i <;> simp [hmn]
    · simp [Fin.prod_univ_four]
  · refine diagHom_mem_statedSU hq0 _ (fun i => ?_) ?_
    · fin_cases i <;> simp [hmn]
    · simp [Fin.prod_univ_four]
  · refine diagHom_mem_statedSU hq0 _ (fun i => ?_) ?_
    · fin_cases i <;> simp [hmn]
    · simp [Fin.prod_univ_four]
  · rw [card_statedSU_four h, hord, factorization_su4_two h3 hq2]

end CFSG.ClassicalInvolution.Asc77.SCH
