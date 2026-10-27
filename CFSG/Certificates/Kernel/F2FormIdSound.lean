module

public import Certificates.Data.Kernel.F2FormId
public import CFSG.Certificates.Kernel.F2AlgRankSound

public section

namespace CFSG.KC.F2FormId

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.F2W CFSG.KC.F2TriSep CFSG.Sporadic.SmallF2
open scoped Matrix

theorem altK_facts {d M : Nat} (h : altK d M = true) :
    (rowsMatrix d (unpackR d M))ᵀ = rowsMatrix d (unpackR d M) ∧
      ∀ i, rowsMatrix d (unpackR d M) i i = 0 := by
  unfold altK at h
  obtain ⟨h1, h2⟩ := F2AlgRank.sepK_andB h
  refine ⟨by rw [← F2AlgRank.unpackR_mat_trK, Nat.eq_of_beq_eq_true h1], fun i => ?_⟩
  have hi := F2AlgRank.sepK_allN h2 i.val i.isLt
  beta_reduce at hi
  have hb : CFSG.KLie.CT.bit M (Nat.add (Nat.mul d i.val) i.val) = false := by
    revert hi
    cases CFSG.KLie.CT.bit M (Nat.add (Nat.mul d i.val) i.val) <;> simp [CFSG.KLie.CT.notB]
  rw [bit_eq] at hb
  change M.testBit (d * i.val + i.val) = false at hb
  rw [F2AlgRank.unpackR_mat_apply, hb]
  rfl

theorem invQK_facts {d Q A : Nat} (h : invQK d Q A = true) :
    ((rowsMatrix d (unpackR d A))ᵀ * rowsMatrix d (unpackR d Q) * rowsMatrix d (unpackR d A) +
        rowsMatrix d (unpackR d Q))ᵀ =
      (rowsMatrix d (unpackR d A))ᵀ * rowsMatrix d (unpackR d Q) * rowsMatrix d (unpackR d A) +
        rowsMatrix d (unpackR d Q) ∧
    ∀ i, ((rowsMatrix d (unpackR d A))ᵀ * rowsMatrix d (unpackR d Q) *
        rowsMatrix d (unpackR d A) + rowsMatrix d (unpackR d Q)) i i = 0 := by
  have hf := altK_facts (d := d) (M := Nat.xor (mulW d (mulW d (trK d A) Q) A) Q) h
  rwa [F2AlgRank.unpackR_mat_xor, F2AlgRank.unpackR_mat_mulW, F2AlgRank.unpackR_mat_mulW,
    F2AlgRank.unpackR_mat_trK] at hf

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem quad_alt {d : Nat} (M : Matrix (Fin d) (Fin d) (ZMod 2)) (hs : Mᵀ = M)
    (hd : ∀ i, M i i = 0) (x : Fin d → ZMod 2) : x ⬝ᵥ (M *ᵥ x) = 0 := by
  classical
  let L : Matrix (Fin d) (Fin d) (ZMod 2) := Matrix.of fun i j => if i < j then M i j else 0
  have hML : M = L + Lᵀ := by
    ext i j
    simp only [L, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij, not_lt.2 hij.le]
    · simp [hd]
    · have e : M i j = M j i := by
        rw [← Matrix.transpose_apply M j i, hs]
      simp [hij, not_lt.2 hij.le, e]
  rw [hML, Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_mulVec x Lᵀ,
    Matrix.vecMul_transpose, dotProduct_comm (L *ᵥ x) x, zmod2_add_self]

theorem invQK_sound {d Q A : Nat} (h : invQK d Q A = true) (x : Fin d → ZMod 2) :
    (rowsMatrix d (unpackR d A) *ᵥ x) ⬝ᵥ
        (rowsMatrix d (unpackR d Q) *ᵥ (rowsMatrix d (unpackR d A) *ᵥ x)) =
      x ⬝ᵥ (rowsMatrix d (unpackR d Q) *ᵥ x) := by
  obtain ⟨hs, hd⟩ := invQK_facts h
  have h0 := quad_alt _ hs hd x
  rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose] at h0
  have h1 := congrArg (· + x ⬝ᵥ (rowsMatrix d (unpackR d Q) *ᵥ x)) h0
  beta_reduce at h1
  rwa [add_assoc, zmod2_add_self, add_zero, zero_add] at h1

theorem fixSumK_facts (d : Nat) (P : List (Nat × Nat)) :
    rowsMatrix d (unpackR d (fixSumK d P)) =
      (P.map fun e => (rowsMatrix d (unpackR d e.1) - 1) * rowsMatrix d (unpackR d e.2)).sum := by
  induction P with
  | nil =>
    change rowsMatrix d (unpackR d 0) = _
    rw [F2AlgRank.unpackR_mat_zero, List.map_nil, List.sum_nil]
  | cons e P ih =>
    obtain ⟨M, X⟩ := e
    change rowsMatrix d (unpackR d (Nat.xor (mulW d (Nat.xor M (idF d)) X) (fixSumK d P))) = _
    rw [F2AlgRank.unpackR_mat_xor, F2AlgRank.unpackR_mat_mulW, F2AlgRank.unpackR_mat_xor,
      F2AlgRank.unpackR_mat_idF, ih, List.map_cons, List.sum_cons]
    dsimp only
    congr 2
    ext i j
    rw [Matrix.add_apply, Matrix.sub_apply, CharTwo.sub_eq_add]

theorem fixSumK_sound {d : Nat} {P : List (Nat × Nat)} {c : Fin d → ZMod 2}
    (hc : ∀ e ∈ P, c ᵥ* rowsMatrix d (unpackR d e.1) = c) :
    c ᵥ* rowsMatrix d (unpackR d (fixSumK d P)) = 0 := by
  rw [fixSumK_facts]
  induction P with
  | nil => simp
  | cons e P ih =>
    rw [List.map_cons, List.sum_cons, Matrix.vecMul_add,
      ih fun e' he' => hc e' (List.mem_cons_of_mem _ he'), add_zero, ← Matrix.vecMul_vecMul,
      Matrix.vecMul_sub, Matrix.vecMul_one, hc e List.mem_cons_self, sub_self, Matrix.zero_vecMul]

end CFSG.KC.F2FormId

end
