module

public import Certificates.Data.Kernel.F2AlgRank
public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.Certificates.Kernel.Co1BTrSound

public section

namespace CFSG.KC.F2AlgRank

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.F2W CFSG.Sporadic.SmallF2
open scoped Matrix

theorem sepK_andB {a b : Bool} (h : CFSG.KLie.CT.andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KLie.CT.andB]

theorem sepK_allN {n : Nat} {f : Nat → Bool} (h : CFSG.KLie.CT.allN n f = true) :
    ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have h' : CFSG.KLie.CT.andB (f n) (CFSG.KLie.CT.allN n f) = true := h
    obtain ⟨h1, h2⟩ := sepK_andB h'
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem sepK_nIf (c : Bool) (t e : Nat) : Bool.rec (motive := fun _ => Nat) e t c = if c then t else e := by
  cases c <;> rfl

theorem sepK_strictB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem sepK_pw2 (n : Nat) : CFSG.KLie.CT.pw2 n = 2 ^ n := Nat.one_shiftLeft n

theorem unpackR_mat_apply (d X : Nat) (i j : Fin d) :
    rowsMatrix d (unpackR d X) i j = if X.testBit (d * i.val + j.val) then 1 else 0 := by
  rw [rowsMatrix_apply, toVecD_apply]
  have e : (unpackR d X)[i.val]? = some (X / 2 ^ (d * i.val) % 2 ^ d) := by
    simp [unpackR, i.isLt]
  rw [e, Option.getD_some, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j.val]
  simp [j.isLt]

theorem unpackR_mat_zero (d : Nat) : rowsMatrix d (unpackR d 0) = 0 := by
  ext i j
  rw [unpackR_mat_apply]
  simp

theorem unpackR_mat_xor (d X Y : Nat) :
    rowsMatrix d (unpackR d (Nat.xor X Y)) = rowsMatrix d (unpackR d X) + rowsMatrix d (unpackR d Y) := by
  have e : Nat.xor X Y = X ^^^ Y := rfl
  ext i j
  rw [Matrix.add_apply, unpackR_mat_apply, unpackR_mat_apply, unpackR_mat_apply, e, Nat.testBit_xor]
  cases X.testBit (d * i.val + j.val) <;> cases Y.testBit (d * i.val + j.val) <;> decide

theorem unpackR_mat_mulW (d A B : Nat) :
    rowsMatrix d (unpackR d (mulW d A B)) = rowsMatrix d (unpackR d A) * rowsMatrix d (unpackR d B) := by
  rw [← mulRows_unpackW, rowsMatrix_mulRows]

theorem unpackR_mat_trK (d A : Nat) :
    rowsMatrix d (unpackR d (trK d A)) = (rowsMatrix d (unpackR d A))ᵀ := by
  rw [← transposeRows_unpackR, rowsMatrix_transposeRows]

theorem unpackR_mat_idF (d : Nat) : rowsMatrix d (unpackR d (idF d)) = 1 := by
  ext i j
  rw [rowsMatrix_apply, Matrix.one_apply]
  have h : rowF d (idF d) i.val = CFSG.KLie.CT.pw2 i.val :=
    rowF_orN d (f := CFSG.KLie.CT.pw2) (fun k hk => by
      rw [sepK_pw2]
      exact Nat.pow_lt_pow_right (by norm_num) hk) i.isLt
  rw [rowF_eq, sepK_pw2] at h
  have e : (unpackR d (idF d))[i.val]? = some (2 ^ i.val) := by
    simp [unpackR, i.isLt, h]
  rw [e, Option.getD_some, toVecD_apply, Nat.testBit_two_pow]
  by_cases hij : i = j
  · subst hij
    simp
  · have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    simp [hij, hij']

theorem unpackR_mat_mulVec (d M v : Nat) :
    rowsMatrix d (unpackR d M) *ᵥ toVecD d v = toVecD d (vmF d (trK d M) v) := by
  rw [rowsMatrix_mulVec, transposeRows_unpackR, vecMulN_unpackR]

theorem mulVec_row {d : Nat} (F : Nat) (v : Fin d → ZMod 2) (k : Fin d) :
    (rowsMatrix d (unpackR d F) *ᵥ v) k = toVecD d (rowF d F k) ⬝ᵥ v := by
  have e : (unpackR d F)[k.val]? = some (rowF d F k) := by
    simp [unpackR, rowF_eq, k.isLt]
  simp only [Matrix.mulVec, dotProduct, rowsMatrix_apply, e, Option.getD_some]

theorem getL_zero_or_mem : ∀ (L : List Nat) (i : Nat), getL 0 L i = 0 ∨ getL 0 L i ∈ L
  | [], _ => Or.inl rfl
  | _ :: _, 0 => Or.inr List.mem_cons_self
  | a :: L, i + 1 => (getL_zero_or_mem L i).imp id (List.mem_cons_of_mem a)

section Alg

variable {d : Nat} {A : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2))}

theorem getL_mat_mem {L : List Nat} (hL : ∀ x ∈ L, rowsMatrix d (unpackR d x) ∈ A) (i : Nat) :
    rowsMatrix d (unpackR d (getL 0 L i)) ∈ A := by
  rcases getL_zero_or_mem L i with h | h
  · rw [h, unpackR_mat_zero]
    exact A.zero_mem
  · exact hL _ h

theorem algK_mem {G : List Nat} (hG : ∀ g ∈ G, rowsMatrix d (unpackR d g) ∈ A)
    {k : List Nat → Bool} : ∀ (tree : List (Nat × Nat)) (acc : List Nat),
    algK d G tree acc k = true → (∀ x ∈ acc, rowsMatrix d (unpackR d x) ∈ A) →
      ∃ L, k L = true ∧ ∀ x ∈ L, rowsMatrix d (unpackR d x) ∈ A
  | [], acc, h, hacc => ⟨acc, h, hacc⟩
  | (o, g) :: tree, acc, h, hacc => by
    have h' : strictB (mulW d (getL 0 G g) (getL 0 acc o))
        (fun M => algK d G tree (M :: acc) k) = true := h
    rw [sepK_strictB] at h'
    refine algK_mem hG tree _ h' ?_
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [unpackR_mat_mulW]
      exact A.mul_mem (getL_mat_mem hG g) (getL_mat_mem hacc o)
    · exact hacc x hx

theorem selK_mem : ∀ (L : List Nat) (m : Nat), (∀ x ∈ L, rowsMatrix d (unpackR d x) ∈ A) →
    rowsMatrix d (unpackR d (selK L m)) ∈ A
  | [], _, _ => by
    change rowsMatrix d (unpackR d 0) ∈ A
    rw [unpackR_mat_zero]
    exact A.zero_mem
  | x :: L, m, hL => by
    change rowsMatrix d (unpackR d (Nat.xor (Bool.rec (motive := fun _ => Nat) 0 x
      (CFSG.KLie.CT.bit m 0)) (selK L (Nat.shiftRight m 1)))) ∈ A
    rw [unpackR_mat_xor, sepK_nIf]
    refine A.add_mem ?_ (selK_mem L _ fun y hy => hL y (List.mem_cons_of_mem _ hy))
    split
    · exact hL x List.mem_cons_self
    · rw [unpackR_mat_zero]
      exact A.zero_mem

end Alg

theorem rk2K_mulVec {d T t w r s : Nat} (h : rk2K d T t w r s = true) (v : Fin d → ZMod 2) :
    rowsMatrix d (unpackR d T) *ᵥ v =
      (toVecD d r ⬝ᵥ v) • toVecD d t + (toVecD d s ⬝ᵥ v) • toVecD d w := by
  unfold rk2K at h
  funext i
  have hi := sepK_allN h i.val i.isLt
  beta_reduce at hi
  have e := Nat.eq_of_beq_eq_true hi
  have hx : ∀ a b : Nat, toVecD d (Nat.xor a b) = toVecD d a + toVecD d b := fun a b =>
    toVecD_xor d a b
  rw [mulVec_row, e, sepK_nIf, sepK_nIf, bit_eq, bit_eq, hx, add_dotProduct,
    Pi.add_apply, Pi.smul_apply, Pi.smul_apply, toVecD_apply, toVecD_apply]
  cases t.testBit i.val <;> cases w.testBit i.val <;> simp [toVecD_zero]

theorem sepK_facts {d : Nat} {G : List Nat} {tree : List (Nat × Nat)} {masks S : List Nat}
    {F Dm t w : Nat} (h : sepK d G tree masks S F Dm t w = true) :
    ∃ Y : Nat → Matrix (Fin d) (Fin d) (ZMod 2),
      (∀ k < d - 1, Y k ∈ Algebra.adjoin (ZMod 2) {X | ∃ g ∈ G, X = rowsMatrix d (unpackR d g)}) ∧
      (∀ k < d - 1, ∀ v, Y k *ᵥ v = (toVecD d (rowF d F k) ⬝ᵥ v) • toVecD d t +
        (toVecD d (getL 0 S k) ⬝ᵥ v) • toVecD d w) ∧
      rowsMatrix d (unpackR d Dm) * rowsMatrix d (unpackR d F) = 1 ∧
      rowsMatrix d (unpackR d Dm) *ᵥ toVecD d (2 ^ (d - 1)) = toVecD d w := by
  obtain ⟨L, hk, hL⟩ := algK_mem (A := Algebra.adjoin (ZMod 2)
      {X | ∃ g ∈ G, X = rowsMatrix d (unpackR d g)})
    (fun g hg => Algebra.subset_adjoin ⟨g, hg, rfl⟩) tree [idF d] h (by
      intro x hx
      rw [List.mem_singleton.1 hx, unpackR_mat_idF]
      exact Subalgebra.one_mem _)
  obtain ⟨h1, h23⟩ := sepK_andB hk
  obtain ⟨h2, h3⟩ := sepK_andB h23
  have hd : Nat.pred d = d - 1 := Nat.pred_eq_sub_one
  rw [hd] at h1 h3
  refine ⟨fun k => rowsMatrix d (unpackR d (selK L (getL 0 masks k))), fun k _ => selK_mem L _ hL,
    fun k hk v => rk2K_mulVec (sepK_allN h1 k hk) v, ?_, ?_⟩
  · rw [← unpackR_mat_mulW, Nat.eq_of_beq_eq_true h2, unpackR_mat_idF]
  · rw [unpackR_mat_mulVec, ← sepK_pw2, Nat.eq_of_beq_eq_true h3]

@[expose] def stabAlg {d : Nat} (U : Submodule (ZMod 2) (Fin d → ZMod 2)) :
    Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)) where
  carrier := {X | ∀ u ∈ U, X *ᵥ u ∈ U}
  mul_mem' {X Y} hX hY u hu := by
    rw [← Matrix.mulVec_mulVec]
    exact hX _ (hY u hu)
  add_mem' {X Y} hX hY u hu := by
    rw [Matrix.add_mulVec]
    exact U.add_mem (hX u hu) (hY u hu)
  algebraMap_mem' r u hu := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact U.smul_mem r hu

theorem sepK_sound {d : Nat} {G : List Nat} {tree : List (Nat × Nat)} {masks S : List Nat}
    {F Dm t w : Nat} (h : sepK d G tree masks S F Dm t w = true)
    (U : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hG : ∀ g ∈ G, ∀ u ∈ U, rowsMatrix d (unpackR d g) *ᵥ u ∈ U) (hw : toVecD d w ∈ U)
    {y : Fin d → ZMod 2} (hy : y ∈ U) (hyw : y ∉ Submodule.span (ZMod 2) {toVecD d w}) :
    toVecD d t ∈ U := by
  obtain ⟨Y, hYalg, hY, hinv, hcol⟩ := sepK_facts h
  have hpres : ∀ k < d - 1, ∀ u ∈ U, Y k *ᵥ u ∈ U := by
    intro k hk
    have hle : Algebra.adjoin (ZMod 2) {X | ∃ g ∈ G, X = rowsMatrix d (unpackR d g)} ≤
        stabAlg U := by
      refine Algebra.adjoin_le ?_
      rintro X ⟨g, hg, rfl⟩
      exact hG g hg
    exact hle (hYalg k hk)
  by_contra hne
  apply hyw
  have hz : ∀ k < d - 1, toVecD d (rowF d F k) ⬝ᵥ y = 0 := by
    intro k hk
    by_contra h1
    have h1' : toVecD d (rowF d F k) ⬝ᵥ y = 1 := by
      generalize toVecD d (rowF d F k) ⬝ᵥ y = a at h1
      revert a
      decide
    apply hne
    have hm := hpres k hk y hy
    rw [hY k hk y, h1', one_smul] at hm
    exact (Submodule.add_mem_iff_left U (U.smul_mem (toVecD d (getL 0 S k) ⬝ᵥ y) hw)).1 hm
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Subsingleton.elim y 0]
    exact Submodule.zero_mem _
  have hFy : rowsMatrix d (unpackR d F) *ᵥ y =
      (rowsMatrix d (unpackR d F) *ᵥ y) ⟨d - 1, by omega⟩ • toVecD d (2 ^ (d - 1)) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, toVecD_apply, Nat.testBit_two_pow]
    by_cases hi : i.val = d - 1
    · have e : i = ⟨d - 1, by omega⟩ := Fin.ext hi
      rw [e]
      simp
    · have hi' : ¬ (d - 1 = i.val) := fun e => hi e.symm
      rw [mulVec_row, hz i (by omega)]
      simp [hi']
  have hyD : y = rowsMatrix d (unpackR d Dm) *ᵥ (rowsMatrix d (unpackR d F) *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [Submodule.mem_span_singleton]
  refine ⟨(rowsMatrix d (unpackR d F) *ᵥ y) ⟨d - 1, by omega⟩, ?_⟩
  calc (rowsMatrix d (unpackR d F) *ᵥ y) ⟨d - 1, by omega⟩ • toVecD d w
      = rowsMatrix d (unpackR d Dm) *ᵥ ((rowsMatrix d (unpackR d F) *ᵥ y) ⟨d - 1, by omega⟩ •
          toVecD d (2 ^ (d - 1))) := by rw [Matrix.mulVec_smul, hcol]
    _ = y := by rw [← hFy, ← hyD]

end CFSG.KC.F2AlgRank

end
