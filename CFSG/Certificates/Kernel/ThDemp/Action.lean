module

public import CFSG.Certificates.Kernel.ThDemp.Key
public import CFSG.Certificates.Kernel.ThDemp.Rows
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.Certificates.ThDemp.Act

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThDemp Key Rows

abbrev V := Fin 248 → ZMod 2

abbrev Pts : Type := Submodule (ZMod 2) V

@[expose] def mapM (M : Matrix (Fin 248) (Fin 248) (ZMod 2)) (W : Pts) : Pts :=
  Submodule.map (Matrix.vecMulLinear M) W

theorem mapM_one (W : Pts) : mapM 1 W = W := by
  change Submodule.map (Matrix.vecMulLinear 1) W = W
  have : Matrix.vecMulLinear (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) = LinearMap.id := by
    ext v
    simp [Matrix.vecMulLinear]
  rw [this, Submodule.map_id]

theorem mapM_mul (M N : Matrix (Fin 248) (Fin 248) (ZMod 2)) (W : Pts) :
    mapM (M * N) W = mapM N (mapM M W) := by
  change Submodule.map (Matrix.vecMulLinear (M * N)) W =
    Submodule.map (Matrix.vecMulLinear N) (Submodule.map (Matrix.vecMulLinear M) W)
  have e : Matrix.vecMulLinear (M * N) = (Matrix.vecMulLinear N).comp (Matrix.vecMulLinear M) :=
    LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.vecMulLinear_apply,
        Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul]
  rw [e, Submodule.map_comp]

instance : MulAction (GL (Fin 248) (ZMod 2)) Pts where
  smul g W := mapM ((g⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) W
  one_smul W := by
    change mapM _ W = W
    rw [inv_one, Units.val_one, mapM_one]
  mul_smul g h W := by
    change mapM _ W = mapM _ (mapM _ W)
    rw [mul_inv_rev, Units.val_mul, mapM_mul]

theorem smul_def (g : GL (Fin 248) (ZMod 2)) (W : Pts) :
    g • W = mapM ((g⁻¹ : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) W := rfl

theorem smul_eq_self_iff (g : GL (Fin 248) (ZMod 2)) (W : Pts) :
    g • W = W ↔ mapM (g : Matrix (Fin 248) (Fin 248) (ZMod 2)) W = W := by
  rw [smul_def]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [← mapM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mapM_one]
  · intro h
    conv_lhs => rw [← h]
    rw [← mapM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mapM_one]

theorem smul_eq_iff (g : GL (Fin 248) (ZMod 2)) (W W' : Pts) :
    g • W = W' ↔ W = mapM (g : Matrix (Fin 248) (Fin 248) (ZMod 2)) W' := by
  rw [smul_def]
  constructor
  · rintro rfl
    rw [← mapM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mapM_one]
  · rintro rfl
    rw [← mapM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mapM_one]

@[expose] noncomputable def sp (P : ℕ) : Pts := spanL (rowsOf (2 ^ 248 - 1) P)

theorem pkVec_vecB' (v M : ℕ) :
    pkVec (vecB (2 ^ 248 - 1) v M) = Matrix.vecMul (pkVec v) (pkMat M) := by
  funext j
  rw [pkVec_apply, testBit_vecB]
  have hj := j.isLt
  have hd : decide (j.val < 248) = true := by simp [hj]
  rw [hd, Bool.true_and]
  simp only [Matrix.vecMul, dotProduct]
  have key : ∀ n, n ≤ 248 → (if xsB (fun k => v.testBit k && M.testBit (256 * k + j.val)) n
      then (1 : ZMod 2) else 0) = ∑ k ∈ Finset.range n,
        (if v.testBit k && M.testBit (256 * k + j.val) then 1 else 0) := by
    intro n _
    induction n with
    | zero => simp [xsB]
    | succ n ih =>
      rw [xsB, Finset.sum_range_succ, ← ih (by omega)]
      cases xsB (fun k => v.testBit k && M.testBit (256 * k + j.val)) n <;>
        cases v.testBit n && M.testBit (256 * n + j.val) <;> decide
  rw [key 248 le_rfl, ← Fin.sum_univ_eq_sum_range (fun k => if v.testBit k &&
    M.testBit (256 * k + j.val) then (1 : ZMod 2) else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pkVec_apply, pkMat_apply]
  cases v.testBit k.val <;> cases M.testBit (256 * k.val + j.val) <;> simp

theorem rowsOf_mulB (P N : ℕ) :
    rowsOf (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) =
      (rowsOf (2 ^ 248 - 1) P).map (fun r => vecB (2 ^ 248 - 1) r N) := by
  have h := fun r (hr : r < 5) => row_mulB (n := 5) hr P N
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  simp only [Nat.mul_zero, Nat.shiftRight_zero] at h0
  simp only [rowsOf, List.map_cons, List.map_nil]
  change [_, _, _, _, _] = [_, _, _, _, _]
  have h0' : Nat.land (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) (2 ^ 248 - 1) = _ := h0
  have h1' : Nat.land (Nat.shiftRight (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) 256) (2 ^ 248 - 1) = _ :=
    h1
  have h2' : Nat.land (Nat.shiftRight (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) 512) (2 ^ 248 - 1) = _ :=
    h2
  have h3' : Nat.land (Nat.shiftRight (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) 768) (2 ^ 248 - 1) = _ :=
    h3
  have h4' : Nat.land (Nat.shiftRight (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) 1024) (2 ^ 248 - 1) =
    _ := h4
  rw [h0', h1', h2', h3', h4']
  rfl

theorem spanL_map (l : List ℕ) (N : ℕ) :
    spanL (l.map (fun r => vecB (2 ^ 248 - 1) r N)) = mapM (pkMat N) (spanL l) := by
  rw [spanL, spanL, mapM, Submodule.map_span]
  congr 1
  ext v
  simp only [List.mem_map, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨pkVec r, ⟨r, hr, rfl⟩, by rw [pkVec_vecB']; rfl⟩
  · rintro ⟨w, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by rw [pkVec_vecB']; rfl⟩

theorem sp_mulB (P N : ℕ) : sp (mulB (rep 1 256 5) (2 ^ 248 - 1) P N) = mapM (pkMat N) (sp P) := by
  rw [sp, rowsOf_mulB, spanL_map]
  rfl

theorem lil_map {M : Matrix (Fin 248) (Fin 248) (ZMod 2)} {M' : Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (hM : M * M' = 1) (N : ℕ) (hN : pkMat N = M) :
    ∀ l : List ℕ, LIL l → LIL (l.map (fun r => vecB (2 ^ 248 - 1) r N))
  | [], _ => trivial
  | b :: l, ⟨hb, hl⟩ => by
    refine ⟨?_, lil_map hM N hN l hl⟩
    intro hmem
    apply hb
    have h1 := spanL_map l N
    rw [h1, mapM] at hmem
    obtain ⟨w, hw, e⟩ := Submodule.mem_map.mp hmem
    rw [pkVec_vecB', hN] at e
    have e2 : w = pkVec b := by
      have := congrArg (fun u => Matrix.vecMul u M') e
      simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, hM, Matrix.vecMul_one] at this
      exact this
    rw [← e2]
    exact hw

theorem lil_mulB {P N : ℕ} {M' : Matrix (Fin 248) (Fin 248) (ZMod 2)} (hM : pkMat N * M' = 1)
    (hP : LIL (rowsOf (2 ^ 248 - 1) P)) :
    LIL (rowsOf (2 ^ 248 - 1) (mulB (rep 1 256 5) (2 ^ 248 - 1) P N)) := by
  rw [rowsOf_mulB]
  exact lil_map hM N rfl _ hP

theorem land_rm_lt (x : ℕ) : x &&& (2 ^ 248 - 1) < 2 ^ 248 :=
  Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) (by omega))

theorem pkVec_combRow (Q G k : ℕ) : pkVec (combRow (2 ^ 248 - 1) Q G k) ∈ sp Q := by
  let f : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc => Nat.xor acc (Nat.mul (bitsN G (Nat.add (Nat.mul 5 k) j) 1)
      (Nat.land (Nat.shiftRight Q (Nat.mul 256 j)) (2 ^ 248 - 1)))) n
  have hf : ∀ n, f (n + 1) = f n ^^^ Nat.mul (bitsN G (Nat.add (Nat.mul 5 k) n) 1)
      (Nat.land (Nat.shiftRight Q (Nat.mul 256 n)) (2 ^ 248 - 1)) := fun n => rfl
  have key : ∀ n, n ≤ 5 → pkVec (f n) ∈ sp Q := by
    intro n hn
    induction n with
    | zero =>
      change pkVec 0 ∈ sp Q
      rw [pkVec_zero]
      exact Submodule.zero_mem _
    | succ n ih =>
      rw [hf, pkVec_xor]
      refine Submodule.add_mem _ (ih (by omega)) ?_
      have hb : bitsN G (Nat.add (Nat.mul 5 k) n) 1 = 0 ∨ bitsN G (Nat.add (Nat.mul 5 k) n) 1 = 1 := by
        rw [bitsN_eq, pow_one]
        omega
      have hrow : pkVec (Nat.land (Nat.shiftRight Q (Nat.mul 256 n)) (2 ^ 248 - 1)) ∈ sp Q := by
        apply Submodule.subset_span
        refine ⟨_, ?_, rfl⟩
        have : n < 5 := by omega
        interval_cases n <;> simp [rowsOf]
      rcases hb with h | h
      · rw [h]
        change pkVec (0 * _) ∈ sp Q
        rw [Nat.zero_mul, pkVec_zero]
        exact Submodule.zero_mem _
      · rw [h]
        change pkVec (1 * _) ∈ sp Q
        rw [Nat.one_mul]
        exact hrow
  exact key 5 le_rfl

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem sp_le_of_combChk {P Q G : ℕ} (h : combChk (2 ^ 248 - 1) P Q G = true) : sp P ≤ sp Q := by
  have hrows : ∀ k < 5, Nat.land (Nat.shiftRight P (Nat.mul 256 k)) (2 ^ 248 - 1) =
      combRow (2 ^ 248 - 1) Q G k := by
    let g : ℕ → Bool := fun n => Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB (Nat.beq (Nat.land (Nat.shiftRight P (Nat.mul 256 k)) (2 ^ 248 - 1))
        (combRow (2 ^ 248 - 1) Q G k)) ih) n
    have hg : ∀ n, g (n + 1) = andB (Nat.beq (Nat.land (Nat.shiftRight P (Nat.mul 256 n))
        (2 ^ 248 - 1)) (combRow (2 ^ 248 - 1) Q G n)) (g n) := fun n => rfl
    have key : ∀ n, g n = true → ∀ k < n, Nat.land (Nat.shiftRight P (Nat.mul 256 k)) (2 ^ 248 - 1) =
        combRow (2 ^ 248 - 1) Q G k := by
      intro n
      induction n with
      | zero => intro _ k hk; omega
      | succ n ih =>
        intro hn k hk
        rw [hg] at hn
        obtain ⟨h1, h2⟩ := andB_eq_true hn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact ih h2 k hk
        · exact Nat.eq_of_beq_eq_true h1
    exact key 5 h
  rw [sp, spanL, Submodule.span_le]
  rintro v ⟨b, hb, rfl⟩
  simp only [rowsOf, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · have h0 : Nat.land P (2 ^ 248 - 1) = combRow (2 ^ 248 - 1) Q G 0 := hrows 0 (by omega)
    rw [h0]
    exact pkVec_combRow Q G 0
  · have e : Nat.land (Nat.shiftRight P 256) (2 ^ 248 - 1) = _ := hrows 1 (by omega)
    rw [e]
    exact pkVec_combRow Q G 1
  · have e : Nat.land (Nat.shiftRight P 512) (2 ^ 248 - 1) = _ := hrows 2 (by omega)
    rw [e]
    exact pkVec_combRow Q G 2
  · have e : Nat.land (Nat.shiftRight P 768) (2 ^ 248 - 1) = _ := hrows 3 (by omega)
    rw [e]
    exact pkVec_combRow Q G 3
  · have e : Nat.land (Nat.shiftRight P 1024) (2 ^ 248 - 1) = _ := hrows 4 (by omega)
    rw [e]
    exact pkVec_combRow Q G 4

theorem sp_eq_image (P : ℕ) :
    ((sp P : Submodule (ZMod 2) V) : Set V) = pkVec '' {x | x ∈ combsL (rowsOf (2 ^ 248 - 1) P) 0} := by
  ext v
  constructor
  · intro hv
    obtain ⟨x, hx, e⟩ := exists_combs _ 0 v hv
    rw [pkVec_zero, zero_add] at e
    exact ⟨x, hx, e⟩
  · rintro ⟨x, hx, rfl⟩
    have := (mem_combs _ 0 (Nat.two_pow_pos _) (rowsOf_lt P) x hx).2
    rw [pkVec_zero, sub_zero] at this
    exact this

theorem ncard_sp {P : ℕ} (hP : LIL (rowsOf (2 ^ 248 - 1) P)) :
    ((sp P : Submodule (ZMod 2) V) : Set V).ncard = 32 := by
  classical
  rw [sp_eq_image, Set.InjOn.ncard_image]
  · have hnd := nodup_combs _ 0 (rowsOf_lt P) (Nat.two_pow_pos _) hP
    have e : {x | x ∈ combsL (rowsOf (2 ^ 248 - 1) P) 0} =
        ((combsL (rowsOf (2 ^ 248 - 1) P) 0).toFinset : Set ℕ) := by
      ext
      simp
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    rfl
  · intro x hx y hy e
    exact pkVec_inj (mem_combs _ 0 (Nat.two_pow_pos _) (rowsOf_lt P) x hx).1
      (mem_combs _ 0 (Nat.two_pow_pos _) (rowsOf_lt P) y hy).1 e

theorem sp_eq_of_combChk {P Q G : ℕ} (h : combChk (2 ^ 248 - 1) P Q G = true)
    (hP : LIL (rowsOf (2 ^ 248 - 1) P)) (hQ : LIL (rowsOf (2 ^ 248 - 1) Q)) : sp P = sp Q := by
  have hle := sp_le_of_combChk h
  have hfin : ((sp Q : Submodule (ZMod 2) V) : Set V).Finite := Set.toFinite _
  have heq : ((sp P : Submodule (ZMod 2) V) : Set V) = ((sp Q : Submodule (ZMod 2) V) : Set V) :=
    Set.eq_of_subset_of_ncard_le hle (by rw [ncard_sp hP, ncard_sp hQ]) hfin
  exact SetLike.coe_injective heq

theorem keyL_eq {P Q : ℕ} (hP : LIL (rowsOf (2 ^ 248 - 1) P)) (hQ : LIL (rowsOf (2 ^ 248 - 1) Q))
    (h : sp P = sp Q) : keyL (2 ^ 248 - 1) P = keyL (2 ^ 248 - 1) Q :=
  keyL_eq_of_span hP hQ h

end CFSG.Certificates.ThDemp.Act

end
