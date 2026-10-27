module

public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.Quasithin CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Finset

@[expose] def gfBit (v : ℕ) (a : GF8) : ZMod 2 := if a.toNat.testBit v then 1 else 0

@[expose] def gfX (u : ℕ) : GF8 := GF8.ofNat' (2 ^ u)

theorem gfBit_add (v : Fin 3) (a b : GF8) : gfBit v (a + b) = gfBit v a + gfBit v b := by
  revert v a b
  decide

theorem gfBit_zero (v : Fin 3) : gfBit v 0 = 0 := by
  revert v
  decide

theorem gfBit_mul (v : Fin 3) (a b : GF8) :
    gfBit v (a * b) = gfBit 0 a * gfBit v (gfX 0 * b) + gfBit 1 a * gfBit v (gfX 1 * b) +
      gfBit 2 a * gfBit v (gfX 2 * b) := by
  revert v a b
  decide

theorem eq_of_gfBit (a b : GF8) (h : ∀ v : Fin 3, gfBit v a = gfBit v b) : a = b := by
  revert a b
  decide

theorem gfX_zero : gfX 0 = 1 := by decide

@[expose] def gfBitHom (v : Fin 3) : GF8 →+ ZMod 2 where
  toFun := gfBit v
  map_zero' := gfBit_zero v
  map_add' := gfBit_add v

theorem gfBit_sum (v : Fin 3) {ι : Type*} (s : Finset ι) (f : ι → GF8) :
    gfBit v (∑ k ∈ s, f k) = ∑ k ∈ s, gfBit v (f k) :=
  map_sum (gfBitHom v) f s

@[expose] def blk (p : Fin 24) : Fin 8 := ⟨p.val / 3, by omega⟩

@[expose] def epsM (M : Matrix (Fin 8) (Fin 8) GF8) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  Matrix.of fun p q => gfBit (q.val % 3) (gfX (p.val % 3) * M (blk p) (blk q))

@[expose] def idx24 (k : Fin 8) (w : Fin 3) : Fin 24 := ⟨3 * k.val + w.val, by omega⟩

theorem blk_idx24 (k : Fin 8) (w : Fin 3) : blk (idx24 k w) = k := by
  apply Fin.ext
  simp only [blk, idx24]
  omega

theorem mod_idx24 (k : Fin 8) (w : Fin 3) : (idx24 k w).val % 3 = w.val := by
  simp only [idx24]
  omega

theorem sum_fin24 {A : Type*} [AddCommMonoid A] (f : Fin 24 → A) :
    ∑ r, f r = ∑ k : Fin 8, ∑ w : Fin 3, f (idx24 k w) := by
  rw [← Fintype.sum_prod_type']
  let e : Fin 8 × Fin 3 ≃ Fin 24 := finProdFinEquiv
  have he : ∀ x : Fin 8 × Fin 3, e x = idx24 x.1 x.2 := by
    intro x
    apply Fin.ext
    show x.2.val + 3 * x.1.val = 3 * x.1.val + x.2.val
    ring
  rw [← Equiv.sum_comp e f]
  exact Finset.sum_congr rfl fun x _ => by rw [he]

theorem epsM_mul (M N : Matrix (Fin 8) (Fin 8) GF8) : epsM (M * N) = epsM M * epsM N := by
  ext p q
  set u := p.val % 3
  set v : Fin 3 := ⟨q.val % 3, Nat.mod_lt _ (by norm_num)⟩ with hv
  simp only [epsM, Matrix.of_apply, Matrix.mul_apply]
  rw [sum_fin24, Finset.mul_sum, show q.val % 3 = v.val from rfl, gfBit_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, gfBit_mul v, Fin.sum_univ_three]
  simp only [blk_idx24, mod_idx24]
  rfl

theorem epsM_one : epsM 1 = 1 := by
  decide

theorem epsM_injective : Function.Injective epsM := by
  intro M N h
  ext i j
  apply eq_of_gfBit
  intro v
  have h1 := congrFun (congrFun h (idx24 i 0)) (idx24 j v)
  simp only [epsM, Matrix.of_apply, blk_idx24, mod_idx24] at h1
  rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, gfX_zero, one_mul, one_mul] at h1
  exact h1

@[expose] def epsHom : Matrix (Fin 8) (Fin 8) GF8 →* Matrix (Fin 24) (Fin 24) (ZMod 2) where
  toFun := epsM
  map_one' := epsM_one
  map_mul' := epsM_mul

@[expose] def encRows (M : Matrix (Fin 8) (Fin 8) GF8) : Array ℕ :=
  Array.ofFn (n := 24) fun p => ofBits 24 fun q =>
    if h : q < 24 then (gfX (p.val % 3) * M (blk p) (blk ⟨q, h⟩)).toNat.testBit (q % 3)
    else false

theorem rowsMatrix_encRows (M : Matrix (Fin 8) (Fin 8) GF8) :
    rowsMatrix 24 (encRows M) = epsM M := by
  ext p q
  rw [rowsMatrix_apply]
  simp only [encRows, Array.getElem?_ofFn, p.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_ofBits]
  simp only [q.isLt, ↓reduceDIte, epsM, Matrix.of_apply, gfBit]

@[expose] def validR (R : Array ℕ) : Bool :=
  R.size == 24 && (List.range 24).all fun i => decide (R[i]! < 2 ^ 24)

theorem getElem?_getD_of_lt {R : Array ℕ} {i : ℕ} (h : i < R.size) : R[i]?.getD 0 = R[i]! := by
  rw [getElem!_pos R i h, Array.getElem?_eq_getElem h, Option.getD_some]

theorem eq_of_rowsMatrix_eq {R S : Array ℕ} (hR : validR R = true) (hS : validR S = true)
    (h : rowsMatrix 24 R = rowsMatrix 24 S) : R = S := by
  simp only [validR, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hR hS
  apply Array.ext (hR.1.trans hS.1.symm)
  intro i hi hi'
  have h24 : i < 24 := hR.1 ▸ hi
  have hrow : toVecD 24 (R[i]?.getD 0) = toVecD 24 (S[i]?.getD 0) := by
    funext j
    exact congrFun (congrFun h ⟨i, h24⟩) j
  rw [getElem?_getD_of_lt hi, getElem?_getD_of_lt hi'] at hrow
  have := toVecD_injective (hR.2 i h24) (hS.2 i h24) hrow
  rwa [getElem!_pos R i hi, getElem!_pos S i hi'] at this

end CFSG.LargeExtraspecial.S63
