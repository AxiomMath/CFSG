module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix

theorem toVec_two_pow (n : ℕ) (j : Fin n) : toVec n (2 ^ (j : ℕ)) = Pi.single j 1 := by
  ext i
  rw [toVec, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp
  · rw [Pi.single_eq_of_ne h]
    have : (j : ℕ) ≠ i := fun e => h (Fin.ext e.symm)
    simp [this]

@[expose] def linBits (n p : ℕ) (Fb : ℕ → ℕ) : Array ℕ :=
  btr n p (Array.ofFn (n := n) fun j => Fb (2 ^ (j : ℕ)))

theorem toMat_linBits_mulVec {n p : ℕ} (Fb : ℕ → ℕ)
    (F : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin p → ZMod 2))
    (hF : ∀ j : Fin n, toVec p (Fb (2 ^ (j : ℕ))) = F (Pi.single j 1)) (y : Fin n → ZMod 2) :
    toMat p n (linBits n p Fb) *ᵥ y = F y := by
  have h : (toMat p n (linBits n p Fb)).mulVecLin = F := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.single_apply, mulVecLin_apply]
    rw [← hF j]
    ext i
    rw [mulVec_single_one, linBits, toMat_btr]
    simp only [col_apply, transpose_apply, toMat_apply, getD_ofFn, toVec]
  rw [← h, mulVecLin_apply]

@[expose] def lead (v : ℕ) : ℕ := Nat.log2 v

@[expose] def reduce (piv : List (ℕ × ℕ)) (v t : ℕ) : ℕ × ℕ :=
  piv.foldl (fun acc q => if acc.1.testBit (lead q.1) then (acc.1 ^^^ q.1, acc.2 ^^^ q.2) else acc)
    (v, t)

@[expose] def insertPiv : List (ℕ × ℕ) → ℕ × ℕ → List (ℕ × ℕ)
  | [], q => [q]
  | r :: rest, q => if lead r.1 < lead q.1 then q :: r :: rest else r :: insertPiv rest q

@[expose] def addPiv (piv : List (ℕ × ℕ)) (v t : ℕ) : List (ℕ × ℕ) :=
  let r := reduce piv v t
  if r.1 = 0 then piv else insertPiv piv r

@[expose] def addPivRec (acc : List (ℕ × ℕ) × List ℕ) (v t l : ℕ) : List (ℕ × ℕ) × List ℕ :=
  let r := reduce acc.1 v t
  if r.1 = 0 then acc else (insertPiv acc.1 r, l :: acc.2)

@[expose] def certEQ (n m p : ℕ) (R Bcols : Array ℕ) : Array ℕ × Array ℕ :=
  let piv0 := (List.range m).foldl (fun piv j => addPiv piv (Bcols.getD j 0) (2 ^ j)) []
  let acc := (List.range n).foldl (fun acc l => addPivRec acc (2 ^ l) (2 ^ (m + l)) l) (piv0, [])
  let piv1 := acc.1
  let Ecols := Array.ofFn (n := n) fun l => (reduce piv1 (2 ^ (l : ℕ)) 0).2 % 2 ^ m
  let Rc := btr p n R
  let pivQ0 := acc.2.foldl (fun piv l => addPiv piv (Rc.getD l 0) (2 ^ l)) []
  let pivQ := (List.range p).foldl (fun piv q => addPiv piv (2 ^ q) (2 ^ (n + q))) pivQ0
  let Qcols := Array.ofFn (n := p) fun q => (reduce pivQ (2 ^ (q : ℕ)) 0).2 % 2 ^ n
  (btr n m Ecols, btr p n Qcols)

@[expose] def certQ (n p : ℕ) (R : Array ℕ) : Array ℕ :=
  let Rc := btr p n R
  let pivQ0 := (List.range n).foldl (fun piv l => addPiv piv (Rc.getD l 0) (2 ^ l)) []
  let pivQ := (List.range p).foldl (fun piv q => addPiv piv (2 ^ q) (2 ^ (n + q))) pivQ0
  let Qcols := Array.ofFn (n := p) fun q => (reduce pivQ (2 ^ (q : ℕ)) 0).2 % 2 ^ n
  btr p n Qcols

@[expose] def certCheck (n m p : ℕ) (R Bcols : Array ℕ) : Bool :=
  let EQ := certEQ n m p R Bcols
  bIsId n (bxor n (bmul n m (btr m n Bcols) EQ.1) (bmul n p EQ.2 R))

@[expose] def injCheck (n p : ℕ) (R : Array ℕ) : Bool :=
  bIsId n (bmul n p (certQ n p R) R)

theorem cert_eq_one {n m p : ℕ} {R Bcols : Array ℕ} (h : certCheck n m p R Bcols = true) :
    toMat n m (btr m n Bcols) * toMat m n (certEQ n m p R Bcols).1 +
      toMat n p (certEQ n m p R Bcols).2 * toMat p n R = 1 := by
  rw [← toMat_bmul, ← toMat_bmul, ← toMat_bxor]
  exact toMat_eq_one_of_bIsId h

theorem inj_eq_one {n p : ℕ} {R : Array ℕ} (h : injCheck n p R = true) :
    toMat n p (certQ n p R) * toMat p n R = 1 := by
  rw [← toMat_bmul]
  exact toMat_eq_one_of_bIsId h

theorem exists_eq_mulVec_of_certCheck {n m p : ℕ} {R Bcols : Array ℕ}
    (h : certCheck n m p R Bcols = true) {c : Fin n → ZMod 2} (hc : toMat p n R *ᵥ c = 0) :
    ∃ e : Fin m → ZMod 2, c = (toMat m n Bcols)ᵀ *ᵥ e := by
  refine ⟨toMat m n (certEQ n m p R Bcols).1 *ᵥ c, ?_⟩
  rw [← toMat_btr]
  exact eq_mulVec_of_cert (cert_eq_one h) hc

theorem eq_zero_of_injCheck {n p : ℕ} {R : Array ℕ} (h : injCheck n p R = true)
    {c : Fin n → ZMod 2} (hc : toMat p n R *ᵥ c = 0) : c = 0 :=
  eq_zero_of_cert (inj_eq_one h) hc

@[expose] def unpackBlk (v s : ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun a => bitsOf 8 fun b => v.testBit (64 * s + 8 * (a : ℕ) + b)

@[expose] def packBlks (k : ℕ) (f : ℕ → Array ℕ) : ℕ :=
  let b := Array.ofFn (n := k) fun s => f s
  bitsOf (k * 64) fun i => ((b.getD (i / 64) #[]).getD (i % 64 / 8) 0).testBit (i % 8)

@[expose] def blocksOf (k : ℕ) (y : Fin (k * 64) → ZMod 2) :
    Fin k → Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  fun s => Matrix.of fun a b => y (finProdFinEquiv (s, finProdFinEquiv (a, b)))

@[expose] def vecOf (k : ℕ) (C : Fin k → Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    Fin (k * 64) → ZMod 2 :=
  fun i => C (finProdFinEquiv.symm i).1
    ((finProdFinEquiv (m := 8) (n := 8)).symm (finProdFinEquiv.symm i).2).1
    ((finProdFinEquiv (m := 8) (n := 8)).symm (finProdFinEquiv.symm i).2).2

theorem blocksOf_vecOf (k : ℕ) (C : Fin k → Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    blocksOf k (vecOf k C) = C := by
  ext s a b
  simp [blocksOf, vecOf]

theorem vecOf_blocksOf (k : ℕ) (y : Fin (k * 64) → ZMod 2) : vecOf k (blocksOf k y) = y := by
  ext i
  simp only [vecOf, blocksOf, Matrix.of_apply, Prod.mk.eta, Equiv.apply_symm_apply]

@[expose] def blocksEquiv (k : ℕ) :
    (Fin (k * 64) → ZMod 2) ≃ₗ[ZMod 2] (Fin k → Matrix (Fin 8) (Fin 8) (ZMod 2)) where
  toFun := blocksOf k
  invFun := vecOf k
  map_add' y z := by ext; simp [blocksOf]
  map_smul' c y := by ext; simp [blocksOf]
  left_inv := vecOf_blocksOf k
  right_inv := blocksOf_vecOf k

theorem blocksEquiv_apply (k : ℕ) (y : Fin (k * 64) → ZMod 2) : blocksEquiv k y = blocksOf k y :=
  rfl

theorem blocksEquiv_symm_apply (k : ℕ) (C : Fin k → Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    (blocksEquiv k).symm C = vecOf k C :=
  rfl

theorem toMat_unpackBlk (k v : ℕ) (s : Fin k) :
    toMat 8 8 (unpackBlk v s) = blocksOf k (toVec (k * 64) v) s := by
  ext a b
  rw [toMat_apply, unpackBlk, getD_ofFn, testBit_bitsOf]
  simp only [b.isLt, decide_true, Bool.true_and, blocksOf, Matrix.of_apply, toVec,
    finProdFinEquiv_apply_val]
  congr 2
  ring

theorem toVec_packBlks (k : ℕ) (f : ℕ → Array ℕ) :
    toVec (k * 64) (packBlks k f) = vecOf k fun s => toMat 8 8 (f s) := by
  ext i
  have hi : (i : ℕ) / 64 < k := Nat.div_lt_of_lt_mul (by simp [mul_comm])
  have hb : (Array.ofFn (n := k) fun s => f s).getD ((i : ℕ) / 64) #[] = f ((i : ℕ) / 64) := by
    simp [Array.getD_eq_getD_getElem?, hi]
  simp only [toVec, packBlks, testBit_bitsOf, i.isLt, decide_true, Bool.true_and, vecOf,
    finProdFinEquiv_symm_apply, toMat_apply, Fin.coe_divNat, Fin.coe_modNat, hb]
  have h1 : (i : ℕ) % (8 * 8) = (i : ℕ) % 64 := rfl
  have h2 : (i : ℕ) % 64 % 8 = (i : ℕ) % 8 := Nat.mod_mod_of_dvd _ (by norm_num)
  simp only [h1, h2]

@[expose] def unpackN (n v s : ℕ) : Array ℕ :=
  Array.ofFn (n := n) fun a => bitsOf n fun b => v.testBit (n * n * s + n * (a : ℕ) + b)

@[expose] def packN (n k : ℕ) (f : ℕ → Array ℕ) : ℕ :=
  let b := Array.ofFn (n := k) fun s => f s
  bitsOf (k * (n * n)) fun i => ((b.getD (i / (n * n)) #[]).getD (i % (n * n) / n) 0).testBit (i % n)

@[expose] def blocksOfN (n k : ℕ) (y : Fin (k * (n * n)) → ZMod 2) :
    Fin k → Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun s => Matrix.of fun a b => y (finProdFinEquiv (s, finProdFinEquiv (a, b)))

@[expose] def vecOfN (n k : ℕ) (C : Fin k → Matrix (Fin n) (Fin n) (ZMod 2)) :
    Fin (k * (n * n)) → ZMod 2 :=
  fun i => C (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1
    (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2

theorem blocksOfN_vecOfN (n k : ℕ) (C : Fin k → Matrix (Fin n) (Fin n) (ZMod 2)) :
    blocksOfN n k (vecOfN n k C) = C := by
  ext s a b
  simp [blocksOfN, vecOfN]

theorem vecOfN_blocksOfN (n k : ℕ) (y : Fin (k * (n * n)) → ZMod 2) :
    vecOfN n k (blocksOfN n k y) = y := by
  ext i
  simp only [vecOfN, blocksOfN, Matrix.of_apply, Prod.mk.eta, Equiv.apply_symm_apply]

@[expose] def blocksEquivN (n k : ℕ) :
    (Fin (k * (n * n)) → ZMod 2) ≃ₗ[ZMod 2] (Fin k → Matrix (Fin n) (Fin n) (ZMod 2)) where
  toFun := blocksOfN n k
  invFun := vecOfN n k
  map_add' y z := by ext; simp [blocksOfN]
  map_smul' c y := by ext; simp [blocksOfN]
  left_inv := vecOfN_blocksOfN n k
  right_inv := blocksOfN_vecOfN n k

theorem blocksEquivN_apply (n k : ℕ) (y : Fin (k * (n * n)) → ZMod 2) :
    blocksEquivN n k y = blocksOfN n k y :=
  rfl

theorem blocksEquivN_symm_apply (n k : ℕ) (C : Fin k → Matrix (Fin n) (Fin n) (ZMod 2)) :
    (blocksEquivN n k).symm C = vecOfN n k C :=
  rfl

theorem toMat_unpackN (n k v : ℕ) (s : Fin k) :
    toMat n n (unpackN n v s) = blocksOfN n k (toVec (k * (n * n)) v) s := by
  ext a b
  rw [toMat_apply, unpackN, getD_ofFn, testBit_bitsOf]
  simp only [b.isLt, decide_true, Bool.true_and, blocksOfN, Matrix.of_apply, toVec,
    finProdFinEquiv_apply_val]
  congr 2
  ring

theorem toVec_packN (n k : ℕ) (f : ℕ → Array ℕ) :
    toVec (k * (n * n)) (packN n k f) = vecOfN n k fun s => toMat n n (f s) := by
  ext i
  have hi : (i : ℕ) / (n * n) < k := Nat.div_lt_of_lt_mul (by simp [mul_comm])
  have hb : (Array.ofFn (n := k) fun s => f s).getD ((i : ℕ) / (n * n)) #[] =
      f ((i : ℕ) / (n * n)) := by
    simp [Array.getD_eq_getD_getElem?, hi]
  have h2 : (i : ℕ) % (n * n) % n = (i : ℕ) % n := Nat.mod_mod_of_dvd _ (dvd_mul_right n n)
  simp only [toVec, packN, testBit_bitsOf, i.isLt, decide_true, Bool.true_and, vecOfN,
    finProdFinEquiv_symm_apply, toMat_apply, Fin.coe_divNat, Fin.coe_modNat, hb, h2]

theorem blocksOfN_packN (n k : ℕ) (f : ℕ → Array ℕ) :
    blocksOfN n k (toVec (k * (n * n)) (packN n k f)) = fun s : Fin k => toMat n n (f s) := by
  rw [toVec_packN, blocksOfN_vecOfN]

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
