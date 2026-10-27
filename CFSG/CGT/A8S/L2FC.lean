module

public import CFSG.CGT.A8S.L2Words

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

theorem decA_T : ∀ v < 8, decA (v + 2184) = (v, idC3) := by
  intro v hv
  simp only [decA, idC3, Prod.mk.injEq, Cols3.mk.injEq]
  omega

theorem conj_mem_T0 {x : PG 5 relsN0A8} (hx : x ∈ T0)
    (n : PG 5 relsN0A8) : n * x * n⁻¹ ∈ T0 := by
  rw [mem_T0_iff] at hx ⊢
  obtain ⟨v, hv8, hv⟩ : ∃ v, v < 8 ∧ avc x = v + 2184 :=
    ⟨_, Nat.mod_lt _ (by norm_num), eq_of_isTc hx⟩
  have hxa : affOf (n0Perm x) = (v, idC3) := by rw [← decA_avc, hv, decA_T _ hv8]
  have hxapp : ∀ j : Fin 8, (n0Perm x j).val = v ^^^ j.val := by
    intro j
    rw [n0Perm_apply_val, hxa, applyC3_idC3 j.isLt]
  set C := (affOf (n0Perm n)).2 with hC
  have key : affOf (n0Perm (n * x * n⁻¹)) = (applyC3 C v, idC3) := by
    refine affOf_eq fun i => ?_
    have hj := n0Perm_apply_val n ((n0Perm n)⁻¹ i)
    rw [Equiv.Perm.eq_inv_iff_eq.1 rfl] at hj
    rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      n0Perm_apply_val n, hxapp, applyC3_xor, applyC3_idC3 i.isLt, ← hC, hj]
    rw [← Nat.xor_assoc, Nat.xor_comm _ (applyC3 C v), Nat.xor_assoc]
  have hlt : applyC3 C v < 8 := applyC3_lt (affOf_col_lt _) _
  rw [avc, key]
  simp only [isTc, affCode, idC3, Nat.beq_eq]
  omega

@[expose] def isOrd3 (c : ℕ) : Bool := Nat.beq (cmul c (cmul c c)) 2184 && !Nat.beq c 2184

theorem fc1_check : d0Codes.all (fun c => !isOrd3 c ||
    d0Codes.any (fun e => Nat.beq (cmul e c) (cmul 3675 e))) = true := by
  decide +kernel

@[expose] def d0Words : List (List (Fin 2)) :=
  [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0],
   [1, 0, 1], [1, 1, 0], [1, 1, 1], [0, 0, 1, 0], [0, 0, 1, 1], [0, 1, 0, 0], [0, 1, 0, 1],
   [0, 1, 1, 0], [0, 1, 1, 1], [1, 0, 0, 1], [1, 0, 1, 0], [1, 0, 1, 1], [1, 1, 0, 0],
   [1, 1, 0, 1], [1, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 1, 1, 0], [0, 0, 1, 1, 1],
   [0, 1, 0, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 1, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1],
   [0, 1, 1, 1, 0], [1, 0, 0, 1, 0], [1, 0, 0, 1, 1], [1, 0, 1, 0, 0], [1, 0, 1, 0, 1],
   [1, 0, 1, 1, 0], [1, 0, 1, 1, 1], [1, 1, 0, 0, 1], [1, 1, 0, 1, 1], [1, 1, 1, 0, 0],
   [1, 1, 1, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 1, 0], [0, 0, 1, 0, 1, 1],
   [0, 0, 1, 1, 0, 1], [0, 0, 1, 1, 1, 0], [0, 1, 0, 0, 1, 0], [0, 1, 0, 0, 1, 1],
   [0, 1, 0, 1, 0, 0], [0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 1], [0, 1, 1, 0, 0, 1],
   [0, 1, 1, 1, 0, 0], [0, 1, 1, 1, 0, 1], [1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 1],
   [1, 0, 0, 1, 1, 1], [1, 0, 1, 0, 0, 1], [1, 0, 1, 0, 1, 1], [1, 0, 1, 1, 1, 0],
   [1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 1], [1, 1, 1, 0, 0, 1], [1, 1, 1, 0, 1, 1],
   [0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 1, 1, 0],
   [0, 0, 1, 0, 1, 1, 1], [0, 0, 1, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 0, 1],
   [0, 1, 0, 0, 1, 1, 1], [0, 1, 0, 1, 0, 0, 1], [0, 1, 1, 1, 0, 0, 1], [0, 1, 1, 1, 0, 1, 1],
   [1, 0, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 1, 1, 0], [1, 0, 1, 1, 1, 0, 0],
   [1, 1, 1, 0, 0, 1, 0], [1, 1, 1, 0, 1, 1, 1], [0, 0, 1, 0, 0, 1, 0, 1],
   [0, 0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 1, 1, 1, 0],
   [0, 1, 1, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 1, 0, 1], [1, 0, 1, 1, 1, 0, 0, 1],
   [0, 0, 1, 0, 0, 1, 0, 1, 0], [0, 1, 0, 0, 1, 1, 1, 0, 1]]

@[expose] def aWd : List (List (Fin 2)) := [[0, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 0]]

@[expose] def bWd : List (List (Fin 2)) := [[1, 1], [0, 1, 1, 0, 0]]

theorem aWd_T0 : aWd.all (fun w => isTc (evD 3160 2717 w)) = true := by decide +kernel

theorem bWd_B0 : bWd.all (fun w => b0Codes.contains (evD 3160 2717 w)) = true := by
  decide +kernel

theorem d0Words_ne : (d0Words.drop 1).all (fun w => !Nat.beq (evD 3160 2717 w) 2184) = true := by
  decide +kernel

@[expose] def fcCond (u : ℕ) : Bool :=
  aWd.all (fun w => b0Codes.contains (evD 3675 u w)) && bWd.all (fun w => isTc (evD 3675 u w)) &&
    (d0Words.drop 1).all (fun w => !Nat.beq (evD 3675 u w) 2184)

@[expose] def goodC : List ℕ := [3228, 2254, 2134]

theorem fc2_check : d0Codes.all (fun u => !fcCond u || goodC.contains u) = true := by
  decide +kernel

theorem goodC_spec : cmul (cmul 3675 3228) (cmul 3675 3675) = 2254 ∧
    cmul (cmul (cmul 3675 3675) 3228) 3675 = 2134 ∧ cmul 3675 (cmul 3675 3675) = 2184 ∧
    cmul 3160 (cmul 3160 3160) = 2184 := by
  decide +kernel

end CFSG.CGT.A8S.L2
