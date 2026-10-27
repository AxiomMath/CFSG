module

public import Certificates.Data.Kernel.U38ProjGen

public section

namespace CFSG.KC.U38PG

open CFSG.KC.Loop CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.U38
open scoped Matrix

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nIf_lt {c : Bool} {t e n : Nat} (ht : t < n) (he : e < n) :
    Bool.rec (motive := fun _ => Nat) e t c < n := by
  cases c
  · exact he
  · exact ht

theorem shl_eq (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem lor_shl {x i : Nat} (hx : x < 2 ^ i) (a : Nat) :
    Nat.lor x (Nat.shiftLeft a i) = x + a * 2 ^ i := by
  have h : Nat.shiftLeft a i + x = Nat.lor (Nat.shiftLeft a i) x :=
    Nat.shiftLeft_add_eq_or_of_lt hx a
  have hc : Nat.lor x (Nat.shiftLeft a i) = Nat.lor (Nat.shiftLeft a i) x := Nat.lor_comm x _
  rw [hc, ← h, shl_eq]
  ring

theorem g6_eq (X i : Nat) : g6 X i = X / 2 ^ (6 * i) % 64 := by
  have h := Nat.and_two_pow_sub_one_eq_mod (X >>> (6 * i)) 6
  rw [← Nat.shiftRight_eq_div_pow]
  exact h

theorem g6_lt (X i : Nat) : g6 X i < 64 := by
  rw [g6_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem gm_lt (a b : Nat) : gm a b < 64 := by
  unfold gm
  exact nIf_lt (by norm_num) (nIf_lt (by norm_num) (g6_lt _ _))

theorem gm_spec_fin : ∀ a b : Fin 64,
    GF64.ofNat' (gm a.val b.val) = GF64.ofNat' a.val * GF64.ofNat' b.val := by
  decide +kernel

theorem gm_spec {a b : Nat} (ha : a < 64) (hb : b < 64) :
    GF64.ofNat' (gm a b) = GF64.ofNat' a * GF64.ofNat' b :=
  gm_spec_fin ⟨a, ha⟩ ⟨b, hb⟩

theorem xor_spec_fin : ∀ a b : Fin 64,
    a.val ^^^ b.val < 64 ∧ GF64.ofNat' (a.val ^^^ b.val) = GF64.ofNat' a.val + GF64.ofNat' b.val := by
  decide +kernel

theorem xor_lt {a b : Nat} (ha : a < 64) (hb : b < 64) : Nat.xor a b < 64 :=
  (xor_spec_fin ⟨a, ha⟩ ⟨b, hb⟩).1

theorem xor_spec {a b : Nat} (ha : a < 64) (hb : b < 64) :
    GF64.ofNat' (Nat.xor a b) = GF64.ofNat' a + GF64.ofNat' b :=
  (xor_spec_fin ⟨a, ha⟩ ⟨b, hb⟩).2

theorem ginv_spec_fin : ∀ a : Fin 64, a.val ≠ 0 →
    GF64.ofNat' a.val * GF64.ofNat' (ginv a.val) = 1 := by
  decide +kernel

theorem ginv_spec {a : Nat} (ha : a < 64) (h0 : a ≠ 0) :
    GF64.ofNat' (ginv a) = (GF64.ofNat' a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (ginv_spec_fin ⟨a, ha⟩ h0)

theorem gbar_spec_fin : ∀ a : Fin 64, GF64.ofNat' (gbar a.val) = GF64.barC (GF64.ofNat' a.val) := by
  decide +kernel

theorem gbar_spec {a : Nat} (ha : a < 64) : GF64.ofNat' (gbar a) = GF64.barC (GF64.ofNat' a) :=
  gbar_spec_fin ⟨a, ha⟩

theorem flags_spec_fin : ∀ a : Fin 64, a.val ≠ 0 →
    (Nat.testBit (flagsOf a.val) 0 = true → GF64.ofNat' a.val ^ 21 ≠ 1) ∧
    (Nat.testBit (flagsOf a.val) 1 = true → GF64.ofNat' a.val ^ 9 ≠ 1) := by
  decide +kernel

theorem dot3_lt (a0 a1 a2 b0 b1 b2 : Nat) : dot3 a0 a1 a2 b0 b1 b2 < 64 :=
  xor_lt (gm_lt _ _) (xor_lt (gm_lt _ _) (gm_lt _ _))

theorem dot3_spec {a0 a1 a2 b0 b1 b2 : Nat} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64)
    (k0 : b0 < 64) (k1 : b1 < 64) (k2 : b2 < 64) :
    GF64.ofNat' (dot3 a0 a1 a2 b0 b1 b2) = GF64.ofNat' a0 * GF64.ofNat' b0 +
      GF64.ofNat' a1 * GF64.ofNat' b1 + GF64.ofNat' a2 * GF64.ofNat' b2 := by
  unfold dot3
  rw [xor_spec (gm_lt _ _) (xor_lt (gm_lt _ _) (gm_lt _ _)), xor_spec (gm_lt _ _) (gm_lt _ _),
    gm_spec h0 k0, gm_spec h1 k1, gm_spec h2 k2, add_assoc]

@[expose] noncomputable def decV (v : Nat) : RowVec :=
  (![GF64.ofNat' (g6 v 0), GF64.ofNat' (g6 v 1), GF64.ofNat' (g6 v 2)] : Fin 3 → GF64)

@[expose] noncomputable def decP (m : Nat) : Matrix (Fin 3) (Fin 3) GF64 :=
  Matrix.of fun i j => GF64.ofNat' (g6 m (3 * i.val + j.val))

theorem pack3_eq {x y z : Nat} (hx : x < 64) (hy : y < 64) :
    Nat.lor x (Nat.lor (Nat.shiftLeft y 6) (Nat.shiftLeft z 12)) = x + 64 * y + 4096 * z := by
  have hy' : Nat.shiftLeft y 6 < 2 ^ 12 := by
    rw [shl_eq]
    norm_num
    omega
  rw [lor_shl hy' z]
  have e : Nat.shiftLeft y 6 + z * 2 ^ 12 = Nat.shiftLeft (y + 64 * z) 6 := by
    rw [shl_eq, shl_eq]
    ring
  rw [e, lor_shl (by norm_num; omega : x < 2 ^ 6)]
  ring

theorem g6_pack3 {x y z : Nat} (hx : x < 64) (hy : y < 64) (hz : z < 64) :
    g6 (Nat.lor x (Nat.lor (Nat.shiftLeft y 6) (Nat.shiftLeft z 12))) 0 = x ∧
    g6 (Nat.lor x (Nat.lor (Nat.shiftLeft y 6) (Nat.shiftLeft z 12))) 1 = y ∧
    g6 (Nat.lor x (Nat.lor (Nat.shiftLeft y 6) (Nat.shiftLeft z 12))) 2 = z := by
  rw [pack3_eq hx hy, g6_eq, g6_eq, g6_eq]
  norm_num
  omega

theorem decV_vmP (v m : Nat) : decV (vmP v m) = Matrix.vecMul (decV v) (decP m) := by
  unfold vmP
  simp only [strictN_eq]
  obtain ⟨e0, e1, e2⟩ := g6_pack3 (dot3_lt (g6 v 0) (g6 v 1) (g6 v 2) (g6 m 0) (g6 m 3) (g6 m 6))
    (dot3_lt (g6 v 0) (g6 v 1) (g6 v 2) (g6 m 1) (g6 m 4) (g6 m 7))
    (dot3_lt (g6 v 0) (g6 v 1) (g6 v 2) (g6 m 2) (g6 m 5) (g6 m 8))
  simp only [decV]
  rw [e0, e1, e2]
  funext j
  fin_cases j <;>
    simp [decP, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      dot3_spec (g6_lt _ _) (g6_lt _ _) (g6_lt _ _) (g6_lt _ _) (g6_lt _ _) (g6_lt _ _)]

@[expose] noncomputable def pkn (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t ih => Nat.lor ih (Nat.shiftLeft (f t) (Nat.mul 6 t))) n

theorem pkn_eq (f : Nat → Nat) (hf : ∀ t, f t < 64) (n : Nat) :
    pkn f n = ∑ t ∈ Finset.range n, f t * 2 ^ (6 * t) ∧ pkn f n < 2 ^ (6 * n) := by
  induction n with
  | zero => simp [pkn]
  | succ n ih =>
    have hs : pkn f (n + 1) = Nat.lor (pkn f n) (Nat.shiftLeft (f n) (6 * n)) := rfl
    rw [hs, lor_shl ih.2, Finset.sum_range_succ, ← ih.1]
    refine ⟨rfl, ?_⟩
    have h1 := ih.2
    have h2 := hf n
    have e : 2 ^ (6 * (n + 1)) = 64 * 2 ^ (6 * n) := by rw [Nat.mul_succ, pow_add]; ring
    rw [e]
    nlinarith

theorem g6_pk9 (f : Nat → Nat) (hf : ∀ t, f t < 64) {s : Nat} (hs : s < 9) :
    g6 (pk9 f) s = f s := by
  have h : pk9 f = pkn f 9 := rfl
  rw [h, (pkn_eq f hf 9).1, g6_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have := hf 0
  have := hf 1
  have := hf 2
  have := hf 3
  have := hf 4
  have := hf 5
  have := hf 6
  have := hf 7
  have := hf 8
  interval_cases s <;> norm_num <;> omega

theorem decP_mulP (a b : Nat) : decP (mulP a b) = decP a * decP b := by
  refine Matrix.ext fun i j => ?_
  have hf : ∀ t, entP a b (Nat.div t 3) (Nat.mod t 3) < 64 := fun t => dot3_lt _ _ _ _ _ _
  have hi := i.isLt
  have hj := j.isLt
  simp only [decP, mulP, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three]
  rw [g6_pk9 _ hf (by omega)]
  have h1 : Nat.div (3 * i.val + j.val) 3 = i.val := by
    change (3 * i.val + j.val) / 3 = i.val
    omega
  have h2 : Nat.mod (3 * i.val + j.val) 3 = j.val := by
    change (3 * i.val + j.val) % 3 = j.val
    omega
  rw [h1, h2]
  unfold entP
  rw [dot3_spec (g6_lt _ _) (g6_lt _ _) (g6_lt _ _) (g6_lt _ _) (g6_lt _ _) (g6_lt _ _)]
  fin_cases i <;> fin_cases j <;> rfl

theorem decP_conjTrP (a : Nat) : decP (conjTrP a) = ((decP a).map GF64.barC)ᵀ := by
  refine Matrix.ext fun i j => ?_
  have hf : ∀ t, gbar (g6 a (Nat.add (Nat.mul 3 (Nat.mod t 3)) (Nat.div t 3))) < 64 :=
    fun t => g6_lt _ _
  have hi := i.isLt
  have hj := j.isLt
  simp only [decP, conjTrP, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [g6_pk9 _ hf (by omega), gbar_spec (g6_lt _ _)]
  have h1 : Nat.div (3 * i.val + j.val) 3 = i.val := by
    change (3 * i.val + j.val) / 3 = i.val
    omega
  have h2 : Nat.mod (3 * i.val + j.val) 3 = j.val := by
    change (3 * i.val + j.val) % 3 = j.val
    omega
  rw [h1, h2]
  rfl

end CFSG.KC.U38PG
