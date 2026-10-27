module

public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup

theorem x0_central_aux (n : ℕ) {g : Amb n} (hg : g ∈ Fgrp n) : g * x0 n = x0 n * g :=
  Prod.ext (by simp [x0]) hg.1

theorem x4_cycleType : x4.cycleType = {2, 2} := by
  apply cycleType_swap_mul_swap_of_nodup
  decide

theorem card_centralizer_x4 :
    Nat.card (Subgroup.centralizer ({x4} : Set (Perm (Fin 4)))) = 8 := by
  rw [nat_card_centralizer, x4_cycleType, Fintype.card_fin]
  have : ({2, 2} : Multiset ℕ).toFinset = {2} := by decide
  rw [this]
  simp

theorem swap01_mem_centralizer_x4 :
    swap (0 : Fin 4) 1 ∈ Subgroup.centralizer ({x4} : Set (Perm (Fin 4))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  decide

theorem card_Fgrp_eq (n : ℕ) : Nat.card (Fgrp n) = 4 * n.factorial := by
  classical
  let D : Subgroup (Perm (Fin 4)) := Subgroup.centralizer ({x4} : Set (Perm (Fin 4)))
  let ψ : Perm (Fin n) × D →* ℤˣ :=
    (sign.comp (MonoidHom.fst _ _)) * (sign.comp (D.subtype.comp (MonoidHom.snd _ _)))
  have hψ : ∀ p, ψ p = sign p.1 * sign (p.2 : Perm (Fin 4)) := fun p => rfl
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ψ.range.one_mem
    · refine ⟨(1, ⟨swap 0 1, swap01_mem_centralizer_x4⟩), ?_⟩
      rw [hψ]
      simp
  have h1 : Nat.card ψ.ker * ψ.ker.index = Nat.card (Perm (Fin n) × D) :=
    Subgroup.card_mul_index ψ.ker
  have h2 : ψ.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange]
    simp [Nat.card_eq_fintype_card]
  have h3 : Nat.card (Perm (Fin n) × D) = n.factorial * 8 := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    rw [card_centralizer_x4]
  have h4 : Nat.card (Fgrp n) = Nat.card ψ.ker := by
    refine Nat.card_congr ?_
    have key : ∀ (a : ℤˣ) (b : ℤˣ), a = b ↔ a * b = 1 := by
      intro a b
      rcases Int.units_eq_one_or a with rfl | rfl <;>
        rcases Int.units_eq_one_or b with rfl | rfl <;> decide
    refine
      { toFun := fun p => ⟨(p.1.1, ⟨p.1.2, Subgroup.mem_centralizer_singleton_iff.2 p.2.1⟩), ?_⟩
        invFun := fun q =>
          ⟨(q.1.1, (q.1.2 : Perm (Fin 4))), Subgroup.mem_centralizer_singleton_iff.1 q.1.2.2, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [MonoidHom.mem_ker, hψ, ← key]
      exact p.2.2
    · have := q.2
      rw [MonoidHom.mem_ker, hψ, ← key] at this
      exact this
    · intro p; rfl
    · intro q; rfl
  rw [h3, h2] at h1
  omega

theorem isSylow_T0_aux (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) :
    ∃ P : Sylow 2 (Fgrp n), (P : Subgroup (Fgrp n)).map (Fgrp n).subtype = T0 n := by
  have hcardF : (Nat.card (Fgrp n)).factorization 2 = 6 := by
    rw [card_Fgrp_eq, Nat.factorization_def _ Nat.prime_two]
    rcases hn with rfl | rfl <;> decide +kernel
  have hcard : Nat.card ((T0 n).subgroupOf (Fgrp n)) =
      2 ^ (Nat.card (Fgrp n)).factorization 2 := by
    rw [hcardF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (T0_le_Fgrp n)).toEquiv,
      card_T0_eq n hn]
    norm_num
  refine ⟨Sylow.ofCard _ hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  exact Subgroup.map_subgroupOf_eq_of_le (T0_le_Fgrp n)

end CFSG.GH74.GLS.C3.Layer2.Model
