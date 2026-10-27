module

public import CFSG.GH74.GLS.C3.Layer2.FinModelCard
public import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import CFSG.GH74.GLS.C3.Layer3.AltInvolutions

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.Layer3

theorem emb_one_swap (n : ℕ) (a b : Fin 4) :
    emb n (1, swap a b) = swap (Fin.natAdd n a) (Fin.natAdd n b) := by
  have h : emb n (1, swap a b) =
      (Equiv.permCongrHom finSumFinEquiv) (Perm.sumCongr 1 (swap a b)) := rfl
  rw [h, Perm.sumCongr_one_swap]
  have h2 := Equiv.symm_trans_swap_trans (Sum.inr a : Fin n ⊕ Fin 4) (Sum.inr b) finSumFinEquiv
  rw [finSumFinEquiv_apply_right, finSumFinEquiv_apply_right] at h2
  exact h2

theorem emb_x0 (n : ℕ) :
    emb n (x0 n) =
      swap (Fin.natAdd n 0) (Fin.natAdd n 1) * swap (Fin.natAdd n 2) (Fin.natAdd n 3) := by
  have h : x0 n = (1, swap 0 1) * (1, swap 2 3) := by
    simp [x0, x4]
  rw [h, map_mul, emb_one_swap, emb_one_swap]

theorem emb_x0_cycleType (n : ℕ) : (emb n (x0 n)).cycleType = {2, 2} := by
  rw [emb_x0]
  apply cycleType_swap_mul_swap_of_nodup
  simp [Fin.ext_iff]

@[expose] def xstarA (n : ℕ) : alternatingGroup (Fin (n + 4)) :=
  embA n ⟨x0 n, x0_mem_Fgrp n⟩

theorem xstarA_coe (n : ℕ) :
    ((xstarA n : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = emb n (x0 n) :=
  rfl

theorem orderOf_xstarA (n : ℕ) : orderOf (xstarA n) = 2 := by
  rw [← Subgroup.orderOf_coe, xstarA_coe, ← lcm_cycleType, emb_x0_cycleType]
  simp

theorem numMoved_xstarA (n : ℕ) :
    numMoved ((xstarA n : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4 := by
  rw [xstarA_coe, numMoved_eq_card_support, ← sum_cycleType, emb_x0_cycleType]
  simp

theorem card_centralizer_xstarA (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Subgroup.centralizer ({xstarA n} : Set (alternatingGroup (Fin (n + 4))))) =
      4 * n.factorial := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hτ : sign (emb n (swap a b, 1)) = -1 := by
    rw [sign_emb, sign_swap hab]
    simp
  have hcomm : emb n (swap a b, 1) *
        ((xstarA n : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) =
      ((xstarA n : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) *
        emb n (swap a b, 1) := by
    have h : ((swap a b, 1) : Amb n) * x0 n = x0 n * (swap a b, 1) :=
      Prod.ext (by simp [x0]) (by simp [x0])
    rw [xstarA_coe, ← map_mul, ← map_mul, h]
  have h1 := card_centralizer_alt_mul_two (xstarA n) _ hτ hcomm
  have h2 := card_centralizer_perm_two_two
    ((xstarA n : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4)))
    (by rw [xstarA_coe]; exact emb_x0_cycleType n)
  rw [h2] at h1
  simp only [Nat.add_sub_cancel] at h1
  omega

theorem range_embA_eq (n : ℕ) (hn : 2 ≤ n) :
    (embA n).range = Subgroup.centralizer ({xstarA n} : Set (alternatingGroup (Fin (n + 4)))) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, xstarA, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (x0_central_aux n g.2)
  · rw [card_centralizer_xstarA n hn,
      Nat.card_congr (MonoidHom.ofInjective (embA_injective n)).toEquiv.symm, card_Fgrp_eq]

theorem nonempty_centralizer_mulEquiv_of_isConj {G : Type*} [Group G] {a b : G}
    (h : IsConj a b) :
    Nonempty (Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have key : ∀ g : G, g ∈ Subgroup.centralizer ({a} : Set G) ↔
      c * g * c⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← hc]
    constructor
    · intro hg
      calc c * g * c⁻¹ * (c * a * c⁻¹) = c * (g * a) * c⁻¹ := by group
        _ = c * (a * g) * c⁻¹ := by rw [hg]
        _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group
    · intro hg
      have h2 : c * (g * a) * c⁻¹ = c * (a * g) * c⁻¹ := by
        calc c * (g * a) * c⁻¹ = c * g * c⁻¹ * (c * a * c⁻¹) := by group
          _ = c * a * c⁻¹ * (c * g * c⁻¹) := hg
          _ = c * (a * g) * c⁻¹ := by group
      simpa using h2
  refine ⟨
    { toFun := fun g => ⟨c * g * c⁻¹, (key g).1 g.2⟩
      invFun := fun g => ⟨c⁻¹ * g * c, (key _).2 (by simp [mul_assoc])⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun g h => Subtype.ext (by simp [mul_assoc]) }⟩

theorem fgrp_equiv_centralizer_aux (n : ℕ) (hn : n = 6 ∨ n = 7)
    (y : alternatingGroup (Fin (n + 4))) (hy : orderOf y = 2)
    (h4 : numMoved ((y : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4) :
    Nonempty (↥(Fgrp n) ≃*
      ↥(Subgroup.centralizer ({y} : Set (alternatingGroup (Fin (n + 4)))))) := by
  have hn2 : 2 ≤ n := by omega
  have hconj : IsConj (xstarA n) y :=
    isConj_alternating_of_numMoved_eq (n + 4) _ _ (orderOf_xstarA n) hy
      (by rw [numMoved_xstarA, h4])
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj hconj
  exact ⟨((MonoidHom.ofInjective (embA_injective n)).trans
    (MulEquiv.subgroupCongr (range_embA_eq n hn2))).trans e⟩

end CFSG.GH74.GLS.C3.Layer2.Model
