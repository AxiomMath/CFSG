
module

public import CFSG.Certificates.Kernel.Th.Spec.Big
public import CFSG.Sporadic.Th.KernelInputsBase

public section

namespace CFSG.KC.Th.Spec.FwdPlane

open CFSG.KC.Th CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th.Kernel Pointwise

@[expose] def w1N : ℕ :=
  327208660843949311569856638931134950366718123578765707520623978699011294545

@[expose] def w2N : ℕ :=
  53118203310247861616881865655955129280624587562044029180903589568007838922

theorem wRow1_eq : wRow1 = toRow (pkVec w1N) := rfl

theorem wRow2_eq : wRow2 = toRow (pkVec w2N) := rfl

private theorem wset_eq_four : Wset = {0, wRow1, wRow2, wRow1 + wRow2} :=
  span_pair_eq wRow1 wRow2

private theorem w1N_lt : w1N < 2 ^ 248 := by decide

private theorem w2N_lt : w2N < 2 ^ 248 := by decide

private theorem w1N_ne_zero : w1N ≠ 0 := by decide

private theorem w2N_ne_zero : w2N ≠ 0 := by decide

private theorem orB_eq_or (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

private theorem inW_iff (x w1 w2 : ℕ) :
    inW x w1 w2 = true ↔ x = w1 ∨ x = w2 ∨ x = w1 ^^^ w2 := by
  change orB (Nat.beq x w1) (orB (Nat.beq x w2) (Nat.beq x (w1 ^^^ w2))) = true ↔ _
  rw [orB_eq_or, orB_eq_or, Bool.or_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]

private theorem toRow_pkVec_ne_zero {x : ℕ} (hx : x < 2 ^ 248) (hx0 : x ≠ 0) :
    toRow (pkVec x) ≠ 0 := by
  intro h
  apply hx0
  apply pkVec_inj hx (Nat.two_pow_pos 248)
  rw [pkVec_zero]
  exact h

private theorem pkVec_w1N_mem : toRow (pkVec w1N) ∈ Wset := by
  rw [wset_eq_four, ← wRow1_eq]
  exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

private theorem pkVec_w2N_mem : toRow (pkVec w2N) ∈ Wset := by
  rw [wset_eq_four, ← wRow2_eq]
  exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

private theorem toRow_pkVec_mem_of_inW {x : ℕ} (hx : inW x w1N w2N = true) :
    toRow (pkVec x) ∈ Wset := by
  rcases (inW_iff x w1N w2N).1 hx with rfl | rfl | rfl
  · exact pkVec_w1N_mem
  · exact pkVec_w2N_mem
  · rw [pkVec_xor, toRow_add]
    exact planeW.add_mem pkVec_w1N_mem pkVec_w2N_mem

private theorem inW_of_toRow_pkVec_mem {x : ℕ} (hx : x < 2 ^ 248) (hm : toRow (pkVec x) ∈ Wset)
    (hne : toRow (pkVec x) ≠ 0) : inW x w1N w2N = true := by
  rw [wset_eq_four] at hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rw [inW_iff]
  rcases hm with h0 | h1 | h2 | h3
  · exact absurd h0 hne
  · exact Or.inl (pkVec_inj hx w1N_lt (h1.trans wRow1_eq))
  · exact Or.inr (Or.inl (pkVec_inj hx w2N_lt (h2.trans wRow2_eq)))
  · have e : toRow (pkVec x) = toRow (pkVec (w1N ^^^ w2N)) := by
      rw [h3, pkVec_xor, toRow_add, ← wRow1_eq, ← wRow2_eq]
    exact Or.inr (Or.inr (pkVec_inj hx (Nat.xor_lt_two_pow w1N_lt w2N_lt) e))

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  {J : Subgroup (GL (Fin 248) (ZMod 2))} {inst : MulAction J RowV}

theorem smul_Wset_of_chk (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hsmul : ∀ (g : J) (v : RowV), g • v = toRow (Matrix.vecMul (ofRow v)
      (((g⁻¹ : J) : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))))
    (g : J) {M : ℕ}
    (hM : ((g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) = pkMat M)
    (h1 : chkInW rm w1N M w1N w2N = true) (h2 : chkInW rm w2N M w1N w2N = true) :
    g • Wset = Wset := by
  have hinv : ∀ v : RowV, g⁻¹ • v = toRow (Matrix.vecMul (ofRow v) (pkMat M)) := fun v => by
    rw [hsmul, inv_inv, hM]
  have hw1 : g⁻¹ • wRow1 ∈ Wset := by
    rw [hinv, wRow1_eq, ofRow_toRow, ← pkVec_vecB hk]
    exact toRow_pkVec_mem_of_inW h1
  have hw2 : g⁻¹ • wRow2 ∈ Wset := by
    rw [hinv, wRow2_eq, ofRow_toRow, ← pkVec_vecB hk]
    exact toRow_pkVec_mem_of_inW h2
  have hsub : g⁻¹ • Wset ⊆ Wset := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.1 hy
    rw [wset_eq_four] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · have h0 : g⁻¹ • (0 : RowV) = 0 := by
        rw [hinv]
        exact Matrix.zero_vecMul _
      rw [h0]
      exact planeW.zero_mem
    · exact hw1
    · exact hw2
    · have hadd : g⁻¹ • (wRow1 + wRow2) = g⁻¹ • wRow1 + g⁻¹ • wRow2 := by
        rw [hinv, hinv, hinv]
        exact Matrix.add_vecMul _ _ _
      rw [hadd]
      exact planeW.add_mem hw1 hw2
  have heq : g⁻¹ • Wset = Wset :=
    Set.eq_of_subset_of_ncard_le hsub (Set.ncard_smul_set g⁻¹ Wset).ge
  calc g • Wset = g • (g⁻¹ • Wset) := by rw [heq]
    _ = Wset := smul_inv_smul g Wset

theorem chk_of_smul_Wset (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (hsmul : ∀ (g : J) (v : RowV), g • v = toRow (Matrix.vecMul (ofRow v)
      (((g⁻¹ : J) : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))))
    (g : J) {M : ℕ}
    (hM : ((g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) = pkMat M)
    (h : g • Wset = Wset) :
    chkInW rm w1N M w1N w2N = true ∧ chkInW rm w2N M w1N w2N = true := by
  have hinv : ∀ v : RowV, g⁻¹ • v = toRow (Matrix.vecMul (ofRow v) (pkMat M)) := fun v => by
    rw [hsmul, inv_inv, hM]
  have h' : g⁻¹ • Wset = Wset := by
    calc g⁻¹ • Wset = g⁻¹ • (g • Wset) := by rw [h]
      _ = Wset := inv_smul_smul g Wset
  have h0 : g⁻¹ • (0 : RowV) = 0 := by
    rw [hinv]
    exact Matrix.zero_vecMul _
  have key : ∀ {x : ℕ}, x < 2 ^ 248 → x ≠ 0 → toRow (pkVec x) ∈ Wset →
      chkInW rm x M w1N w2N = true := by
    intro x hx hx0 hxW
    have hm : g⁻¹ • toRow (pkVec x) ∈ Wset := by
      rw [← h']
      exact Set.smul_mem_smul_set hxW
    have hne : g⁻¹ • toRow (pkVec x) ≠ 0 := fun he =>
      toRow_pkVec_ne_zero hx hx0 (MulAction.injective g⁻¹ (he.trans h0.symm))
    rw [hinv, ofRow_toRow, ← pkVec_vecB hk] at hm hne
    exact inW_of_toRow_pkVec_mem (vecB_lt hk x M) hm hne
  exact ⟨key w1N_lt w1N_ne_zero pkVec_w1N_mem, key w2N_lt w2N_ne_zero pkVec_w2N_mem⟩

end CFSG.KC.Th.Spec.FwdPlane

end
