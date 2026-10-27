module

public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.Extra

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.M12Facts

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13

@[expose] def pR2 (p : NF) : Prop :=
  p ∈ [(0, 0, 0, 0), (0, 2, 1, 1), (1, 1, 0, 0), (1, 3, 1, 1), (2, 0, 1, 1), (2, 2, 0, 0),
    (3, 1, 1, 1), (3, 3, 0, 0)]

instance : DecidablePred pR2 := fun p => by unfold pR2; infer_instance

theorem closed_pR2 : NFClosed pR2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem conj_pR2 : ∀ p q : NF, pR2 q → pR2 (nfMul (nfMul p q) (nfInv p)) := by decide +kernel

theorem pR_of_pR2 : ∀ p : NF, pR2 p → pR p := by decide +kernel

@[expose] def r1rep : Fin 3 → NF := ![(3, 1, 0, 0), (1, 1, 1, 0), (0, 2, 1, 0)]

@[expose] def r2rep : Fin 3 → NF := ![(1, 1, 0, 0), (0, 2, 1, 1), (1, 3, 1, 1)]

theorem r1rep_mem : ∀ i, pR1 (r1rep i) := by decide +kernel
theorem r2rep_mem : ∀ i, pR2 (r2rep i) := by decide +kernel
theorem r1rep_sq : ∀ i, nfMul (r1rep i) (r1rep i) = zNF := by decide +kernel
theorem r2rep_sq : ∀ i, nfMul (r2rep i) (r2rep i) = zNF := by decide +kernel

theorem r1rep_dist : ∀ i j, (r1rep i = r1rep j ∨ r1rep i = nfMul (r1rep j) zNF) → i = j := by
  decide +kernel

theorem r2rep_dist : ∀ i j, (r2rep i = r2rep j ∨ r2rep i = nfMul (r2rep j) zNF) → i = j := by
  decide +kernel

theorem r1_points : ∀ p, pR1 p → nfMul p p = zNF →
    ∃ i, p = r1rep i ∨ p = nfMul (r1rep i) zNF := by decide +kernel

theorem r2_points : ∀ p, pR2 p → nfMul p p = zNF →
    ∃ i, p = r2rep i ∨ p = nfMul (r2rep i) zNF := by decide +kernel

theorem R1R2_comm : ∀ p q, pR1 p → pR2 q → nfMul p q = nfMul q p := by decide +kernel

theorem R1R2_inter : ∀ p, pR1 p → pR2 p → p = (0, 0, 0, 0) ∨ p = zNF := by decide +kernel

theorem R_decomp : ∀ p, pR p → ∃ q, pR1 q ∧ ∃ q', pR2 q' ∧ nfMul q q' = p := by decide +kernel

@[expose] def pSame (c : NF × NF) : Prop := (pR1 c.1 ∧ pR1 c.2) ∨ (pR2 c.1 ∧ pR2 c.2)

instance : DecidablePred pSame := fun c => by unfold pSame; infer_instance

theorem q8_pair : ∀ c₁ ∈ rootsZ, ∀ c₂ ∈ rootsZ, nfMul c₁ c₂ ≠ nfMul c₂ c₁ → pSame (c₁, c₂) := by
  decide +kernel

theorem pR_sq_ne_one_of_mem : ∀ p, pR p → nfMul p p ≠ (0, 0, 0, 0) → nfMul p p = zNF := by
  decide +kernel

theorem centralizer_R : ∀ p : NF, (∀ q, pR q → nfMul p q = nfMul q p) → p = (0, 0, 0, 0) ∨ p = zNF := by
  decide +kernel

theorem H0_sq_z_list : ∀ p, pH0 p → nfMul p p = zNF →
    p ∈ [r1rep 0, nfMul (r1rep 0) zNF, r2rep 0, nfMul (r2rep 0) zNF] := by decide +kernel

theorem H0_sq_z (p : NF) (hp : pH0 p) (h : nfMul p p = zNF) :
    p = r1rep 0 ∨ p = nfMul (r1rep 0) zNF ∨ p = r2rep 0 ∨ p = nfMul (r2rep 0) zNF := by
  simpa using H0_sq_z_list p hp h

theorem R1_inner : ∀ e₀ e₁ : Fin 2, ∃ r, pR1 r ∧
    nfMul (nfMul r (r1rep 0)) (nfInv r) =
      (if e₀ = 0 then r1rep 0 else nfMul (r1rep 0) zNF) ∧
    nfMul (nfMul r (r1rep 1)) (nfInv r) =
      (if e₁ = 0 then r1rep 1 else nfMul (r1rep 1) zNF) := by decide +kernel

theorem R2_inner : ∀ e₀ e₁ : Fin 2, ∃ r, pR2 r ∧
    nfMul (nfMul r (r2rep 0)) (nfInv r) =
      (if e₀ = 0 then r2rep 0 else nfMul (r2rep 0) zNF) ∧
    nfMul (nfMul r (r2rep 1)) (nfInv r) =
      (if e₁ = 0 then r2rep 1 else nfMul (r2rep 1) zNF) := by decide +kernel

theorem R1_gen : ∀ p, pR1 p → ∃ m < 4, ∃ n < 2,
    nfMul (nfPow (r1rep 0) m) (nfPow (r1rep 1) n) = p := by decide +kernel

theorem R2_gen : ∀ p, pR2 p → ∃ m < 4, ∃ n < 2,
    nfMul (nfPow (r2rep 0) m) (nfPow (r2rep 1) n) = p := by decide +kernel

theorem x_decomp : ∃ q, (q = r1rep 2 ∨ q = nfMul (r1rep 2) zNF) ∧ ∃ q',
    (q' = r2rep 1 ∨ q' = nfMul (r2rep 1) zNF) ∧ nfMul q q' = (0, 0, 0, 1) := by decide +kernel

@[expose] def q8NF2 : QuaternionGroup 2 → NF
  | .a i => [(0, 0, 0, 0), (1, 1, 0, 0), (2, 2, 0, 0), (3, 3, 0, 0)].getD i.val (0, 0, 0, 0)
  | .xa i => [(0, 2, 1, 1), (3, 1, 1, 1), (2, 0, 1, 1), (1, 3, 1, 1)].getD i.val (0, 0, 0, 0)

theorem q8NF2_mul : ∀ u v : QuaternionGroup 2, q8NF2 (u * v) = nfMul (q8NF2 u) (q8NF2 v) := by
  decide +kernel

theorem q8NF2_pR2 : ∀ u : QuaternionGroup 2, pR2 (q8NF2 u) := by decide +kernel

theorem q8NF2_inj : Function.Injective q8NF2 := by decide +kernel

theorem q8NF2_surj : ∀ p : NF, pR2 p → ∃ u : QuaternionGroup 2, q8NF2 u = p := by decide +kernel

theorem card_pR1 : Nat.card {p : NF // pR1 p} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide +kernel

theorem card_pR2 : Nat.card {p : NF // pR2 p} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide +kernel

theorem Q8_gen : ∀ u : QuaternionGroup 2, ∃ m < 4, ∃ n < 2,
    u = (QuaternionGroup.a 1) ^ m * (QuaternionGroup.xa 0) ^ n := by decide +kernel

theorem Q8_rels : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.xa 0 * QuaternionGroup.xa 0 ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 ≠ 1 ∧
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide +kernel

theorem card_Q8 : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem R1_not_le_R2 : ∃ p, pR1 p ∧ ¬ pR2 p := by decide +kernel

theorem R_conj_R : ∀ p q : NF, pR p → pR q →
    nfMul (nfMul p q) (nfInv p) = q ∨ nfMul (nfMul p q) (nfInv p) = nfMul q zNF := by
  decide +kernel

theorem R1_order4 : ∀ p, pR1 p → p ≠ (0, 0, 0, 0) → p ≠ zNF → nfMul p p = zNF := by
  decide +kernel

theorem R2_order4 : ∀ p, pR2 p → p ≠ (0, 0, 0, 0) → p ≠ zNF → nfMul p p = zNF := by
  decide +kernel

theorem H0_land_R1 : ∀ p, pR1 p → pH0 p → nfMul p p = zNF →
    p = r1rep 0 ∨ p = nfMul (r1rep 0) zNF := by decide +kernel

theorem H0_land_R2 : ∀ p, pR2 p → pH0 p → nfMul p p = zNF →
    p = r2rep 0 ∨ p = nfMul (r2rep 0) zNF := by decide +kernel

theorem zNF_ne_zero : zNF ≠ (0, 0, 0, 0) := by decide +kernel

theorem point00_prod' : ∀ α ∈ [r1rep 0, nfMul (r1rep 0) zNF], ∀ β ∈ [r2rep 0, nfMul (r2rep 0) zNF],
    nfMul α β ∈ [(2, 0, 0, 0), (0, 2, 0, 0)] := by decide +kernel

theorem pU_two_zero : pU (2, 0, 0, 0) := by decide +kernel
theorem pU_zero_two : pU (0, 2, 0, 0) := by decide +kernel

end CFSG.GH74.GLS.Stage1.Thm6.M12Facts
