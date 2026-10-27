module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDPresent

open Subgroup

variable {Γ : Type*} [Group Γ]

structure Rel (a b c : Γ) : Prop where
  a_pow : a ^ 8 = 1
  b_sq : b ^ 2 = 1
  c_sq : c ^ 2 = 1
  b_a : b * a * b⁻¹ = a ^ 3
  c_a : c * a * c⁻¹ = a ^ 5
  c_b : c * b = b * c

@[expose] def nf (a b c : Γ) (i j e : ℕ) : Γ := a ^ i * b ^ j * c ^ e

variable {a b c : Γ}

@[expose] def genA (a b c : Γ) : closure ({a, b, c} : Set Γ) := ⟨a, subset_closure (by simp)⟩

@[expose] def genB (a b c : Γ) : closure ({a, b, c} : Set Γ) := ⟨b, subset_closure (by simp)⟩

@[expose] def genC (a b c : Γ) : closure ({a, b, c} : Set Γ) := ⟨c, subset_closure (by simp)⟩

private lemma b_conj_pow (h : Rel a b c) (j : ℕ) :
    b ^ j * a * (b ^ j)⁻¹ = a ^ (3 ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' b j]
    calc
      b * b ^ j * a * (b * b ^ j)⁻¹
          = b * (b ^ j * a * (b ^ j)⁻¹) * b⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
      _ = b * a ^ (3 ^ j) * b⁻¹ := by rw [ih]
      _ = (b * a * b⁻¹) ^ (3 ^ j) := by rw [← conj_pow]
      _ = (a ^ 3) ^ (3 ^ j) := by rw [h.b_a]
      _ = a ^ (3 * 3 ^ j) := by rw [pow_mul]
      _ = a ^ 3 ^ (j + 1) := by rw [← pow_succ' 3 j]

private lemma c_conj_pow (h : Rel a b c) (e : ℕ) :
    c ^ e * a * (c ^ e)⁻¹ = a ^ (5 ^ e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ' c e]
    calc
      c * c ^ e * a * (c * c ^ e)⁻¹
          = c * (c ^ e * a * (c ^ e)⁻¹) * c⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
      _ = c * a ^ (5 ^ e) * c⁻¹ := by rw [ih]
      _ = (c * a * c⁻¹) ^ (5 ^ e) := by rw [← conj_pow]
      _ = (a ^ 5) ^ (5 ^ e) := by rw [h.c_a]
      _ = a ^ (5 * 5 ^ e) := by rw [pow_mul]
      _ = a ^ 5 ^ (e + 1) := by rw [← pow_succ' 5 e]

private lemma b_pow_mul_a_pow (h : Rel a b c) (j m : ℕ) :
    b ^ j * a ^ m = a ^ (3 ^ j * m) * b ^ j := by
  calc
    b ^ j * a ^ m = (b ^ j * a * (b ^ j)⁻¹) ^ m * b ^ j := by
      rw [conj_pow]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = (a ^ (3 ^ j)) ^ m * b ^ j := by rw [b_conj_pow h]
    _ = a ^ (3 ^ j * m) * b ^ j := by rw [pow_mul]

private lemma c_pow_mul_a_pow (h : Rel a b c) (e m : ℕ) :
    c ^ e * a ^ m = a ^ (5 ^ e * m) * c ^ e := by
  calc
    c ^ e * a ^ m = (c ^ e * a * (c ^ e)⁻¹) ^ m * c ^ e := by
      rw [conj_pow]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = (a ^ (5 ^ e)) ^ m * c ^ e := by rw [c_conj_pow h]
    _ = a ^ (5 ^ e * m) * c ^ e := by rw [pow_mul]

private lemma c_pow_mul_b_pow (h : Rel a b c) (e j : ℕ) :
    c ^ e * b ^ j = b ^ j * c ^ e :=
  ((show Commute c b from h.c_b).pow_pow e j).eq

private lemma b_c_pow_mul_a_pow (h : Rel a b c) (j e m : ℕ) :
    b ^ j * c ^ e * a ^ m = a ^ (3 ^ j * 5 ^ e * m) * b ^ j * c ^ e := by
  calc
    b ^ j * c ^ e * a ^ m = b ^ j * (c ^ e * a ^ m) := by simp only [mul_assoc]
    _ = b ^ j * (a ^ (5 ^ e * m) * c ^ e) := by rw [c_pow_mul_a_pow h]
    _ = (b ^ j * a ^ (5 ^ e * m)) * c ^ e := by simp only [mul_assoc]
    _ = (a ^ (3 ^ j * (5 ^ e * m)) * b ^ j) * c ^ e := by rw [b_pow_mul_a_pow h]
    _ = a ^ (3 ^ j * (5 ^ e * m)) * b ^ j * c ^ e := by simp only [mul_assoc]
    _ = a ^ (3 ^ j * 5 ^ e * m) * b ^ j * c ^ e := by simp only [mul_assoc]

theorem nf_mul (h : Rel a b c) (i j e i' j' e' : ℕ) :
    nf a b c i j e * nf a b c i' j' e' =
      nf a b c (i + 3 ^ j * 5 ^ e * i') (j + j') (e + e') := by
  unfold nf
  calc
    a ^ i * b ^ j * c ^ e * (a ^ i' * b ^ j' * c ^ e')
        = a ^ i * ((b ^ j * c ^ e * a ^ i') * (b ^ j' * c ^ e')) := by
          simp only [mul_assoc]
    _ = a ^ i * ((a ^ (3 ^ j * 5 ^ e * i') * b ^ j * c ^ e) *
          (b ^ j' * c ^ e')) := by rw [b_c_pow_mul_a_pow h]
    _ = a ^ i * (a ^ (3 ^ j * 5 ^ e * i') * (b ^ j * (c ^ e * b ^ j') * c ^ e')) := by
          simp only [mul_assoc]
    _ = a ^ i * (a ^ (3 ^ j * 5 ^ e * i') * (b ^ j * (b ^ j' * c ^ e) * c ^ e')) := by
          rw [c_pow_mul_b_pow h]
    _ = a ^ (i + 3 ^ j * 5 ^ e * i') * b ^ (j + j') * c ^ (e + e') := by
          simp only [pow_add, mul_assoc]

theorem nf_mod (h : Rel a b c) (i j e : ℕ) :
    nf a b c i j e = nf a b c (i % 8) (j % 2) (e % 2) := by
  unfold nf
  rw [pow_eq_pow_mod i h.a_pow, pow_eq_pow_mod j h.b_sq, pow_eq_pow_mod e h.c_sq]

theorem nf_mem_closure (i j e : ℕ) : nf a b c i j e ∈ closure ({a, b, c} : Set Γ) := by
  unfold nf
  have ha : a ∈ ({a, b, c} : Set Γ) := by simp
  have hb : b ∈ ({a, b, c} : Set Γ) := by simp
  have hc : c ∈ ({a, b, c} : Set Γ) := by simp
  exact Subgroup.mul_mem (Subgroup.closure ({a, b, c} : Set Γ))
    (Subgroup.mul_mem (Subgroup.closure ({a, b, c} : Set Γ))
      (Subgroup.pow_mem (Subgroup.closure ({a, b, c} : Set Γ)) (Subgroup.subset_closure ha) i)
      (Subgroup.pow_mem (Subgroup.closure ({a, b, c} : Set Γ)) (Subgroup.subset_closure hb) j))
    (Subgroup.pow_mem (Subgroup.closure ({a, b, c} : Set Γ)) (Subgroup.subset_closure hc) e)

theorem exists_nf_of_mem_closure (h : Rel a b c) {g : Γ} (hg : g ∈ closure ({a, b, c} : Set Γ)) :
    ∃ i j e : ℕ, i < 8 ∧ j < 2 ∧ e < 2 ∧ g = nf a b c i j e := by
  refine Subgroup.closure_induction''
    (p := fun g _ => ∃ i j e : ℕ, i < 8 ∧ j < 2 ∧ e < 2 ∧ g = nf a b c i j e)
    ?_ ?_ ?_ ?_ hg
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by simp [nf]⟩
    · exact ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by simp [nf]⟩
    · exact ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by simp [nf]⟩
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨7, 0, 0, by norm_num, by norm_num, by norm_num, ?_⟩
      have ha : x * x ^ 7 = 1 := by rw [← pow_succ']; exact h.a_pow
      rw [inv_eq_of_mul_eq_one_right ha]
      simp [nf]
    · refine ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
      have hb : x * x = 1 := by simpa only [pow_two] using h.b_sq
      rw [inv_eq_of_mul_eq_one_right hb]
      simp [nf]
    · refine ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, ?_⟩
      have hc : x * x = 1 := by simpa only [pow_two] using h.c_sq
      rw [inv_eq_of_mul_eq_one_right hc]
      simp [nf]
  · exact ⟨0, 0, 0, by norm_num, by norm_num, by norm_num, by simp [nf]⟩
  · intro x y hx hy ihx ihy
    obtain ⟨i, j, e, hi, hj, he, rfl⟩ := ihx
    obtain ⟨i', j', e', hi', hj', he', rfl⟩ := ihy
    refine ⟨(i + 3 ^ j * 5 ^ e * i') % 8, (j + j') % 2, (e + e') % 2,
      Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    rw [nf_mul h]
    exact nf_mod h _ _ _

end CFSG.OddStandard.SmallF3.L33.KD.SDPresent
