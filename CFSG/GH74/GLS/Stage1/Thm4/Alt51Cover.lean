module

public import CFSG.GH74.GLS.Stage1.Thm4.L97a
public import CFSG.GH74.Uniqueness.SU.SU13TA1Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.Alt51

open Subgroup Equiv Equiv.Perm CFSG CFSG.GH74.GLS CFSG.GH74.Uniqueness.SU.SU13.TA
  CFSG.GH74.GLS.Stage1.Thm4.L97

@[expose] def q8Perm : Fin 4 → Perm (Fin 8) :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7]

theorem q8Perm_sq (i : Fin 4) : q8Perm i * q8Perm i = 1 := by
  revert i
  decide

theorem q8Perm_comm (i j : Fin 4) : q8Perm i * q8Perm j = q8Perm j * q8Perm i := by
  revert i j
  decide

theorem q8Perm_ne (i : Fin 4) : q8Perm i ≠ 1 := by
  revert i
  decide

theorem q8Perm_supp (i : Fin 4) : (q8Perm i).support.card = 4 := by
  revert i
  decide

theorem q8Perm_indep : ∀ c : Fin 4 → Fin 2, c ≠ 0 →
    (List.ofFn fun i => q8Perm i ^ (c i : ℕ)).prod ≠ 1 := by
  decide

theorem cycleType_of_sq_four {σ : Perm (Fin 8)} (h2 : σ * σ = 1) (h1 : σ ≠ 1)
    (hs : σ.support.card = 4) : σ.cycleType = {2, 2} := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hm, hord, hs] at hsum
  simp only [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hm1 : m = 1 := by omega
  rw [hm, hord, hm1]
  rfl

theorem q8Perm_ct (i : Fin 4) : (q8Perm i).cycleType = {2, 2} :=
  cycleType_of_sq_four (q8Perm_sq i) (q8Perm_ne i) (q8Perm_supp i)

theorem mem_alt_of_ct_two_two {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.cycleType = {2, 2}) :
    σ ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, hσ]
  decide

theorem ι8_eq_one {n : ℕ} (hn : 8 ≤ n) {σ : Perm (Fin 8)} (h : ι8 hn σ = 1) : σ = 1 := by
  have h1 := cycleType_ι8 hn σ
  rw [h, Equiv.Perm.cycleType_one] at h1
  exact Equiv.Perm.cycleType_eq_zero.1 h1.symm

theorem exists_Q8Q8 {X : Type} [Group X] {n : ℕ} (hn : 8 ≤ n) (hX : IsDoubleCoverOfAlt X n) :
    ∃ (z : X) (a : Fin 4 → X), (∀ y ∈ center X, y = 1 ∨ y = z) ∧ z ∈ center X ∧ z ≠ 1 ∧
      z * z = 1 ∧ (∀ i, a i * a i = z) ∧
      (∀ i j, a i * a j = a j * a i ∨ a i * a j = z * (a j * a i)) ∧
      (∀ c : Fin 4 → Fin 2, c ≠ 0 →
        (List.ofFn fun i => a i ^ (c i : ℕ)).prod ≠ 1 ∧
          (List.ofFn fun i => a i ^ (c i : ℕ)).prod ≠ z) := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨π, hπ, hker⟩ := exists_twoCover hX
  obtain ⟨z, hzc, hz1, hz2, hzk⟩ := hπ.exists_z
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hcen : ∀ y ∈ center X, y = 1 ∨ y = z := fun y hy => hzk y (by rw [hker]; exact hy)
  let σ : Fin 4 → Perm (Fin n) := fun i => ι8 hn (q8Perm i)
  have hσct : ∀ i, (σ i).cycleType = {2, 2} := fun i => by
    show (ι8 hn (q8Perm i)).cycleType = {2, 2}
    rw [cycleType_ι8, q8Perm_ct]
  have hσalt : ∀ i, σ i ∈ alternatingGroup (Fin n) := fun i => mem_alt_of_ct_two_two (hσct i)
  choose a ha using fun i => hπ.surj ⟨σ i, hσalt i⟩
  have hπa : ∀ i, ((π (a i) : alternatingGroup (Fin n)) : Perm (Fin n)) = σ i := fun i => by
    rw [ha i]
  refine ⟨z, a, hcen, hzc, hz1, hzz, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two hn5 (x := a i)
      (by rw [hπa i]; exact hσct i)
    have : a i ^ 2 = z := (hzk _ hk).resolve_left h1
    rw [← this, sq]
  · intro i j
    have hcomm : σ i * σ j = σ j * σ i := by
      show ι8 hn (q8Perm i) * ι8 hn (q8Perm j) = ι8 hn (q8Perm j) * ι8 hn (q8Perm i)
      rw [← map_mul, ← map_mul, q8Perm_comm]
    have hmem : a i * a j * (a j * a i)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, hπa]
      rw [hcomm]
      simp
    rcases hzk _ hmem with h | h
    · left
      have := mul_inv_eq_one.1 h
      exact this
    · right
      have h' : a i * a j = z * (a j * a i) := by
        have := mul_inv_eq_iff_eq_mul.1 h
        exact this
      exact h'
  · intro c hc
    have hprod : ((π (List.ofFn fun i => a i ^ (c i : ℕ)).prod : alternatingGroup (Fin n)) :
        Perm (Fin n)) = ι8 hn (List.ofFn fun i => q8Perm i ^ (c i : ℕ)).prod := by
      have h1 : ((π (List.ofFn fun i => a i ^ (c i : ℕ)).prod : alternatingGroup (Fin n)) :
          Perm (Fin n)) = (List.ofFn fun i => σ i ^ (c i : ℕ)).prod := by
        have := map_list_prod ((alternatingGroup (Fin n)).subtype.comp π)
          (List.ofFn fun i => a i ^ (c i : ℕ))
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, List.map_ofFn, Function.comp_def,
          map_pow, hπa] at this
        exact this
      have h2 : ι8 hn (List.ofFn fun i => q8Perm i ^ (c i : ℕ)).prod =
          (List.ofFn fun i => σ i ^ (c i : ℕ)).prod := by
        have := map_list_prod (ι8 hn) (List.ofFn fun i => q8Perm i ^ (c i : ℕ))
        simp only [List.map_ofFn, Function.comp_def, map_pow] at this
        exact this
      rw [h1, h2]
    have hne : π (List.ofFn fun i => a i ^ (c i : ℕ)).prod ≠ 1 := by
      intro h1
      have h2 : ι8 hn (List.ofFn fun i => q8Perm i ^ (c i : ℕ)).prod = 1 := by
        rw [← hprod, h1]
        rfl
      exact q8Perm_indep c hc (ι8_eq_one hn h2)
    constructor
    · intro h
      apply hne
      rw [h, map_one]
    · intro h
      apply hne
      rw [h]
      exact (MonoidHom.mem_ker.1 (show z ∈ π.ker by rw [hker]; exact hzc))

end CFSG.GH74.GLS.Stage1.Thm4.Alt51
