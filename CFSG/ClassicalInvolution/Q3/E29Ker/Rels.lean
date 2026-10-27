module

public import CFSG.ClassicalInvolution.Q3.E29Ker.Frame
public import CFSG.ClassicalInvolution.Q3.E29Ker.Enum

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data
open CFSG.Certificates.CosetEnumeration

variable {X : Type} [Group X] {φ : X →* AEQ 8} {Q : Set (Subgroup X)}

private theorem rl_sq_inv {x y : X} (h : x * x = y * y) : x * x * y⁻¹ * y⁻¹ = 1 := by
  rw [show x * x * y⁻¹ * y⁻¹ = (x * x) * (y * y)⁻¹ by group, h, mul_inv_cancel]

namespace Lab

variable (F : Lab φ Q)

private theorem rl_a_four (H : Hyp φ Q) : F.a * F.a * F.a * F.a = 1 := by
  have hmem : F.a * F.a * F.a * F.a ∈ F.K1 :=
    F.K1.mul_mem (F.K1.mul_mem (F.K1.mul_mem F.a_mem F.a_mem) F.a_mem) F.a_mem
  have hφ : φ (F.a * F.a * F.a * F.a) = φ 1 := by
    rw [map_one, map_mul, map_mul, map_mul, F.phi_a]
    exact CFSG.ClassicalInvolution.Q3.E29Ker.q8_pow_four
  exact H.injOn F.mem_Q hmem F.K1.one_mem hφ

private theorem rl_a_sq_eq (H : Hyp φ Q) : F.a * F.a = F.b * F.b := by
  have hφ : φ (F.a * F.a) = φ (F.b * F.b) := by
    rw [map_mul, map_mul, F.phi_a, F.phi_b]
    exact CFSG.ClassicalInvolution.Q3.E29Ker.q8_sq_eq
  exact H.injOn F.mem_Q (F.K1.mul_mem F.a_mem F.a_mem) (F.K1.mul_mem F.b_mem F.b_mem) hφ

private theorem rl_b_a_b_a (H : Hyp φ Q) : F.b * F.a * (F.b)⁻¹ * F.a = 1 := by
  have hmem : F.b * F.a * (F.b)⁻¹ * F.a ∈ F.K1 :=
    F.K1.mul_mem (F.K1.mul_mem (F.K1.mul_mem F.b_mem F.a_mem) (F.K1.inv_mem F.b_mem)) F.a_mem
  have hφ : φ (F.b * F.a * (F.b)⁻¹ * F.a) = φ 1 := by
    simp only [map_mul, map_inv, map_one, F.phi_a, F.phi_b]
    exact CFSG.ClassicalInvolution.Q3.E29Ker.q8_conj
  exact H.injOn F.mem_Q hmem F.K1.one_mem hφ

theorem q8_four (H : Hyp φ Q) (j : ℕ) :
    F.gen (2 * j) * F.gen (2 * j) * F.gen (2 * j) * F.gen (2 * j) = 1 := by
  have h := rl_a_four F H
  have e : F.gen (2 * j) * F.gen (2 * j) * F.gen (2 * j) * F.gen (2 * j) =
      F.T j * (F.a * F.a * F.a * F.a) * (F.T j)⁻¹ := by
    rw [F.gen_even j]
    group
  rw [e, h, mul_one, mul_inv_cancel]

theorem q8_sq (H : Hyp φ Q) (j : ℕ) : F.gen (2 * j) * F.gen (2 * j) =
    F.gen (2 * j + 1) * F.gen (2 * j + 1) := by
  have h := rl_a_sq_eq F H
  have e1 : F.gen (2 * j) * F.gen (2 * j) = F.T j * (F.a * F.a) * (F.T j)⁻¹ := by
    rw [F.gen_even j]
    group
  have e2 : F.gen (2 * j + 1) * F.gen (2 * j + 1) = F.T j * (F.b * F.b) * (F.T j)⁻¹ := by
    rw [F.gen_odd j]
    group
  rw [e1, e2, h]

theorem q8_conj (H : Hyp φ Q) (j : ℕ) :
    F.gen (2 * j + 1) * F.gen (2 * j) * (F.gen (2 * j + 1))⁻¹ * F.gen (2 * j) = 1 := by
  have h := rl_b_a_b_a F H
  have e : F.gen (2 * j + 1) * F.gen (2 * j) * (F.gen (2 * j + 1))⁻¹ * F.gen (2 * j) =
      F.T j * (F.b * F.a * (F.b)⁻¹ * F.a) * (F.T j)⁻¹ := by
    rw [F.gen_even j, F.gen_odd j]
    group
  rw [e, h, mul_one, mul_inv_cancel]

private theorem rl_phi_conj {i j k l : ℕ} {W : List ℕ} (hi : i < 56) (hl : 2 * j + l < 56)
    (hrow : mkQ 8 (nG i) * mkQ 8 (nG (2 * j + l)) * (mkQ 8 (nG i))⁻¹ = mkQ 8 (nWord k W)) :
    φ (F.gen i * F.gen (2 * j + l) * (F.gen i)⁻¹) = mkQ 8 (nWord k W) := by
  rw [map_mul, map_mul, map_inv, F.phi_gen hi, F.phi_gen hl]
  exact hrow

private theorem rl_img_mem
    {d : Nat × Nat × Nat × Nat × List Nat} (hd : d ∈ e29ConjData) {l : ℕ} (hl : l < 2) :
    φ (F.gen d.1 * F.gen (2 * d.2.1 + l) * (F.gen d.1)⁻¹) ∈ (F.L d.2.2.2.1).map φ := by
  obtain ⟨hi, hj, -, hk, -⟩ := conjData_bounds d hd
  obtain ⟨d', hd', h1, h2, h3, h4⟩ := conjData_sibling d hd l hl
  obtain ⟨-, -, -, -, hW'⟩ := conjData_bounds d' hd'
  have hrow : mkQ 8 (nG d.1) * mkQ 8 (nG (2 * d.2.1 + l)) * (mkQ 8 (nG d.1))⁻¹ =
      mkQ 8 (nWord d.2.2.2.1 d'.2.2.2.2) := by
    have h := row_eq hd'
    rw [h1, h2, h3, h4] at h
    exact h
  rw [rl_phi_conj F hi (by omega) hrow, ← F.phi_ev hk hW']
  exact Subgroup.mem_map_of_mem φ (F.ev_mem_L _ hW')

theorem conj_row (H : Hyp φ Q)
    {d : Nat × Nat × Nat × Nat × List Nat} (hd : d ∈ e29ConjData) :
    F.gen d.1 * F.gen (2 * d.2.1 + d.2.2.1) * (F.gen d.1)⁻¹ = F.ev d.2.2.2.1 d.2.2.2.2 := by
  obtain ⟨hi, hj, hy, hk, hW⟩ := conjData_bounds d hd
  have hL : conjSub (F.gen d.1) (F.L d.2.1) = F.L d.2.2.2.1 := by
    refine H.conjSub_eq_of_gen (F.L_mem_Q H d.2.1) (F.L_mem_Q H d.2.2.2.1)
      (S := {F.gen (2 * d.2.1), F.gen (2 * d.2.1 + 1)}) ?_ ?_
    · intro x hx
      obtain ⟨W, hW', rfl⟩ := F.mem_L H hj hx
      unfold Lab.ev
      apply Subgroup.list_prod_mem
      intro y hy'
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy'
      have hl2 : l < 2 := localWords29_lt W hW' l hl
      rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · have h0 := rl_img_mem F hd (l := 0) (by norm_num)
        rwa [add_zero] at h0
      · exact rl_img_mem F hd (l := 1) (by norm_num)
  have hmem : F.gen d.1 * F.gen (2 * d.2.1 + d.2.2.1) * (F.gen d.1)⁻¹ ∈ F.L d.2.2.2.1 := by
    rw [← hL]
    exact conj_mem_conjSub (F.gen_mem_L d.2.1 hy)
  have hφ : φ (F.gen d.1 * F.gen (2 * d.2.1 + d.2.2.1) * (F.gen d.1)⁻¹) =
      φ (F.ev d.2.2.2.1 d.2.2.2.2) :=
    (rl_phi_conj F hi (by omega) (row_eq hd)).trans (F.phi_ev hk hW).symm
  exact H.injOn (F.L_mem_Q H d.2.2.2.1) hmem (F.ev_mem_L d.2.2.2.1 hW) hφ

theorem eval_rels (H : Hyp φ Q) :
    ∀ r ∈ e29Rels (), evalWord (codeVal F.gen) r = 1 := by
  intro r hr
  have hr' : r ∈ (List.range 28).flatMap q8Rels29 ++ e29ConjData.map conjRel29 := hr
  rcases List.mem_append.mp hr' with h | h
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp h
    have hmem : evalWord (codeVal F.gen) r ∈ (q8Rels29 j).map (evalWord (codeVal F.gen)) :=
      List.mem_map_of_mem hj
    rw [evalWord_q8Rels29] at hmem
    rcases List.mem_cons.mp hmem with h1 | hmem
    · rw [h1]
      exact F.q8_four H j
    rcases List.mem_cons.mp hmem with h2 | hmem
    · rw [h2]
      exact rl_sq_inv (F.q8_sq H j)
    rw [List.mem_singleton.mp hmem]
    exact F.q8_conj H j
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    rw [evalWord_conjRel29, F.conj_row H hd]
    exact mul_inv_cancel _

end Lab

end CFSG.ClassicalInvolution.Q3.E29Ker
