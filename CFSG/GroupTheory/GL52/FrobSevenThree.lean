module

public import CFSG.GroupTheory.GL52.SylowThree

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

@[expose] def frobDAM : M5 :=
  !![0, 1, 1, 0, 0; 1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def frobDBM : M5 :=
  !![1, 1, 0, 1, 1; 0, 0, 0, 1, 1; 0, 1, 0, 1, 1; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]

@[expose] def frobDCM : M5 :=
  !![0, 1, 0, 0, 1; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 0]

@[expose] def frobD (i j : ℕ) : M5 :=
  if i = 0 then frobDBM else if j = 0 then frobDAM else frobDCM

@[expose] def frobK (i j : ℕ) : ℕ :=
  if i = 0 then (if j = 1 then 2 else 4) else (if i = 1 then 2 else 4)

set_option maxRecDepth 100000 in
theorem frob_matrix_facts : ∀ i j : Fin 3, ¬ ((i : ℕ) = 0 ∧ (j : ℕ) = 0) →
    frobD i j * frobD i j ^ 6 = 1 ∧ frobD i j ≠ 1 ∧
    (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) * frobD i j *
        (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) ^ 2 = frobD i j ^ frobK i j := by
  decide +kernel

theorem frobK_cases (i j : ℕ) : frobK i j = 2 ∨ frobK i j = 4 := by
  unfold frobK
  split_ifs <;> simp

theorem conj_eq_pow_of_matrix {x d : G52} {k : ℕ} (hx : x ^ 3 = 1)
    (h : (x : M5) * (d : M5) * (x : M5) ^ 2 = (d : M5) ^ k) : x * d * x⁻¹ = d ^ k := by
  have hinv : x⁻¹ = x ^ 2 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hx]
  rw [hinv]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h]

theorem exists_frob73 {β : G52} (hβ : orderOf β = 3) :
    ∃ d : G52, d ≠ 1 ∧ d ^ 7 = 1 ∧ ∃ k : ℕ, (k = 2 ∨ k = 4) ∧ β * d * β⁻¹ = d ^ k := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2) (H := syl3R)
    (by rw [syl3_card_R]; norm_num) (fun P => by rw [syl3_card_sylow P]; norm_num)
  have hβp : IsPGroup 3 (Subgroup.zpowers β) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hβ, pow_one])
  obtain ⟨P, hP⟩ := hβp.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow P₀ P
  have hβP : β ∈ (P : Subgroup G52) := hP (Subgroup.mem_zpowers β)
  rw [hc, hP₀] at hβP
  obtain ⟨x, hx, hxβ⟩ := hβP
  have hxβ' : β = c * x * c⁻¹ := hxβ.symm
  have hx3 : x ^ 3 = 1 := syl3_R_cube x hx
  obtain ⟨i, hi, j, hj, rfl⟩ := syl3_mem_R hx
  have hij : ¬ (i = 0 ∧ j = 0) := by
    rintro ⟨rfl, rfl⟩
    rw [pow_zero, pow_zero, mul_one, mul_one, mul_inv_cancel] at hxβ'
    rw [hxβ', orderOf_one] at hβ
    exact absurd hβ (by norm_num)
  have h1 : frobD i j * frobD i j ^ 6 = 1 := (frob_matrix_facts ⟨i, hi⟩ ⟨j, hj⟩ hij).1
  have h2 : frobD i j ≠ 1 := (frob_matrix_facts ⟨i, hi⟩ ⟨j, hj⟩ hij).2.1
  have h3 : (ord3T2M ^ i * syl3TbM ^ j) * frobD i j * (ord3T2M ^ i * syl3TbM ^ j) ^ 2 =
      frobD i j ^ frobK i j := (frob_matrix_facts ⟨i, hi⟩ ⟨j, hj⟩ hij).2.2
  let d₀ : G52 := mk5 (frobD i j) (frobD i j ^ 6) h1
  have hd₀ : (d₀ : M5) = frobD i j := coe_mk5 _ _ _
  have hd₀7 : d₀ ^ 7 = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hd₀, Units.val_one, pow_succ', h1]
  have hd₀1 : d₀ ≠ 1 := by
    intro h
    apply h2
    rw [← hd₀, h, Units.val_one]
  have hconj : (ord3T2 ^ i * syl3Tb ^ j) * d₀ * (ord3T2 ^ i * syl3Tb ^ j)⁻¹ = d₀ ^ frobK i j := by
    refine conj_eq_pow_of_matrix hx3 ?_
    rw [Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b, hd₀]
    exact h3
  refine ⟨c * d₀ * c⁻¹, ?_, ?_, frobK i j, frobK_cases i j, ?_⟩
  · intro h
    apply hd₀1
    have : d₀ = c⁻¹ * (c * d₀ * c⁻¹) * c := by group
    rw [this, h, mul_one, inv_mul_cancel]
  · rw [conj_pow, hd₀7, mul_one, mul_inv_cancel]
  · rw [hxβ', conj_pow, ← hconj]
    group

end CFSG.GroupTheory.GL52
