module

public import CFSG.Certificates.Kernel.Trace6091.ScanOdd
public import Certificates.Data.Kernel.Trace6091.ScanRest

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.MonsterConv.Perm CFSG.Monster.B CFSG.Monster.B.Rep4371
  CFSG.Monster.AxisCount CFSG.Monster.Existence Finset

theorem pairTab_twin :
    Native.pairTab () = ((List.range 276).map fun q => (pairI q, pairJ q)).toArray := by
  decide +kernel

theorem pairTab_get (q : Nat) (hq : q < 276) : (Native.pairTab ())[q]! = (pairI q, pairJ q) := by
  rw [pairTab_twin]
  simp [hq]

theorem octPos_twin : ∀ o < 759, ∀ t < 8,
    ptQ (octQ o) t = (Native.suppList (wordT (octT o))).getD t 0 := by
  decide +kernel

theorem spreadOctT_eq (o : Nat) (ho : o < 759) (m : Nat) :
    spreadOctT (octQ o) m = Native.spreadG (Model.wordN (octT o)) m := by
  unfold Native.spreadG
  rw [native_combN]
  exact combN_loop (fun t => 2 ^ (Native.suppList (Model.wordN (octT o))).getD t 0)
    (fun t => Nat.shiftLeft 1 (ptQ (octQ o) t)) m 8 fun t ht => by
      rw [Nat.shiftLeft_eq', Nat.one_shiftLeft, octPos_twin o ho t ht, wordT_eq]

theorem octCode_twin (a₀ s : Nat) :
    Nat.xor a₀ (selB (bitN (popcT 24 s) 1) 63) =
      a₀ ^^^ (if Native.popcN 24 s / 2 % 2 == 1 then 63 else 0) := by
  rw [bitN_eq, popcT_eq, selB_toNat, native_popcN, Nat.testBit_eq_decide_div_mod_eq, pow_one]
  change a₀ ^^^ _ = _
  by_cases h : Model.popcN 24 s / 2 % 2 = 1 <;> simp [h]

section Perm

variable {P : Nat} {p : Array Nat}

theorem pairD_twin (q : Nat) (hq : q < 276) :
    dualT (Nat.lor (Nat.shiftLeft 1 (pairI q)) (Nat.shiftLeft 1 (pairJ q))) = pairD q := by
  rw [pairD, pairTab_get q hq, dualT_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq', Nat.one_shiftLeft,
    Nat.one_shiftLeft]
  rfl

theorem pairScanT_eq (hP : ∀ i < 24, pe P i = p[i]!) :
    pairScanT P (betaTabT P) = ∑ q ∈ range 276,
      (xTerm p 0 (Model.thetaN 0 ^^^ pairD q) + xTerm p 63 (Model.thetaN 63 ^^^ pairD q)) := by
  unfold pairScanT
  rw [strictZ_eq, strictZ_eq, sumZ_eq, thetaT_eq, thetaT_eq]
  refine sum_congr rfl fun q hq => ?_
  rw [strictZ_eq, pairD_twin q (mem_range.1 hq), xTermT_eq hP, xTermT_eq hP]
  rfl

theorem octRowT_eq (hP : ∀ i < 24, pe P i = p[i]!) (o : Nat) (ho : o < 759) :
    octRowT P (betaTabT P) (octT o) (octQ o) = ∑ m ∈ range 64,
      xTerm p (Native.octCodeG (octT o) (evenT m))
        (Model.dualN (Native.spreadG (Model.wordN (octT o)) (evenT m))) := by
  unfold octRowT
  rw [sumZ_eq]
  refine sum_congr rfl fun m _ => ?_
  rw [strictZ_eq, strictZ_eq, octCode_twin, xTermT_eq hP, dualT_eq, spreadOctT_eq o ho,
    Native.octCodeG, native_wordN]

theorem octScanT_eq (hP : ∀ i < 24, pe P i = p[i]!) (o₀ n : Nat) (h : o₀ + n ≤ 759) :
    octScanT P (betaTabT P) o₀ n = ∑ j ∈ range n, ∑ m ∈ range 64,
      xTerm p (Native.octCodeG (octT (o₀ + j)) (evenT m))
        (Model.dualN (Native.spreadG (Model.wordN (octT (o₀ + j))) (evenT m))) := by
  unfold octScanT
  rw [sumZ_eq]
  refine sum_congr rfl fun j hj => ?_
  rw [strictZ_eq, strictZ_eq, strictZ_eq]
  exact octRowT_eq hP (o₀ + j) (by have := mem_range.1 hj; omega)

theorem sum_chunks (f : ℕ → ℤ) (c K : ℕ) (v : List ℤ)
    (h : ∀ k < K, ∑ j ∈ range c, f (k * c + j) = v.getD k 0) :
    ∑ x ∈ range (K * c), f x = ∑ k ∈ range K, v.getD k 0 := by
  rw [sum_range_mul f c K]
  exact sum_congr rfl fun k hk => h k (mem_range.1 hk)

theorem odd_block (hP : ∀ i < 24, pe P i = p[i]!) (v : List ℤ)
    (h : ∀ k < 8, oddScanT P (betaTabT P) (k * 256) 256 = v.getD k 0) :
    ∑ t ∈ range 2048, ∑ i ∈ range 24, xTerm p (Model.oddCode (2 * t) i) (Model.dualN (2 ^ i)) =
      ∑ k ∈ range 8, v.getD k 0 :=
  sum_chunks (fun t => ∑ i ∈ range 24, xTerm p (Model.oddCode (2 * t) i) (Model.dualN (2 ^ i)))
    256 8 v fun k hk => (oddScanT_eq hP (k * 256) 256).symm.trans (h k hk)

theorem oct_block (hP : ∀ i < 24, pe P i = p[i]!) (v : List ℤ)
    (h : ∀ k < 11, octScanT P (betaTabT P) (k * 69) 69 = v.getD k 0) :
    ∑ o ∈ range 759, ∑ m ∈ range 64,
      xTerm p (Native.octCodeG (octT o) (evenT m))
        (Model.dualN (Native.spreadG (Model.wordN (octT o)) (evenT m))) =
      ∑ k ∈ range 11, v.getD k 0 :=
  sum_chunks (fun o => ∑ m ∈ range 64, xTerm p (Native.octCodeG (octT o) (evenT m))
      (Model.dualN (Native.spreadG (Model.wordN (octT o)) (evenT m))))
    69 11 v fun k hk => (octScanT_eq hP (k * 69) 69 (by omega)).symm.trans (h k hk)

theorem selZ_decide (q : Prop) [Decidable q] (x : Int) :
    selZ (decide q) x = if q then x else 0 := by
  by_cases h : q
  · rw [decide_eq_true h, ite_eq_left h]
    rfl
  · rw [decide_eq_false h, ite_eq_right h]
    rfl

theorem rowCoef_single (x r : Nat) (s : Int) : rowCoef [(x, s)] r = if x = r then s else 0 := by
  simp [rowCoef]

theorem pi0N_even (x : Nat) : Model.pi0N (2 * x) = 2 * x := by
  unfold Model.pi0N
  rw [Nat.testBit_zero]
  simp

theorem wSel_eq (b : Bool) (c' : Nat) (kc : Bool) (r : Nat) :
    wSel b.toNat c' kc.toNat r =
      if (if b then 2048 else 0) + Native.pi0N (Model.pi0N c') / 2 % 2048 = r then
        Native.sgnI (kc ^^ (b && Model.mu0N c')) else 0 := by
  unfold wSel
  rw [beq_eq_decide, beq_eq_decide, selZ_decide, sgnZ_eq, bitN_eq]
  have hmu : Model.mu0N c' = c'.testBit 0 := rfl
  rw [hmu]
  unfold Native.pi0N Model.pi0N
  cases b <;> cases kc <;> rcases Nat.mod_two_eq_zero_or_one c' with hc | hc <;>
    simp [hc, Nat.testBit_zero, selB, Model.sgnI, Native.sgnI]

theorem wRowT_eq (hP : ∀ i < 24, pe P i = p[i]!) (r : Nat) (hr : r < 4096) :
    wRowT P (betaTabT P) (kappaT (betaTabT P) 63) r =
      rowCoef ((Native.monoRows (Native.ePermN p))[r]!) r := by
  rw [monoRows_get _ r hr, rowCoef_single, native_ePermN]
  unfold wRowT Model.ePermN Native.rowEta Native.rowC
  rw [strictZ_eq, strictZ_eq, strictZ_eq, kappaT_eq hP, kappaT_eq hP, permCT_eq hP, pi0N_even]
  have he : r / 2048 = (decide (2048 ≤ r)).toNat := by
    by_cases h : 2048 ≤ r
    · rw [decide_eq_true h]
      change r / 2048 = 1
      omega
    · rw [decide_eq_false h]
      change r / 2048 = 0
      omega
  rw [he, ← toNat_xor]
  exact wSel_eq _ _ _ _

theorem wScanT_eq (hP : ∀ i < 24, pe P i = p[i]!) :
    wScanT P (betaTabT P) = wTr (Native.GD.ofGen (Native.mkCtx ()) (.perm p)) := by
  unfold wScanT
  rw [strictZ_eq, wTr, ofGen_perm, (rfl : (4096 : ℕ) = 64 * 64), sum_range_mul _ 64 64, sumZ_eq]
  refine sum_congr rfl fun h hh => ?_
  rw [sumZ_eq]
  refine sum_congr rfl fun l hl => ?_
  exact wRowT_eq hP (h * 64 + l) (by have := mem_range.1 hh; have := mem_range.1 hl; omega)

theorem permG_getD' (arr : Array ℕ) (i k : ℕ) (hi : i < 24) (hk : k < 24) :
    (Native.permG arr).getD (i * 24 + k) 0 = if arr[i]! = k then 1 else 0 :=
  permG_getD arr ⟨i, hi⟩ ⟨k, hk⟩

theorem latTr_perm (arr : Array ℕ) :
    latTr (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) =
      ∑ i ∈ range 24, if arr[i]! = i then 1 else 0 := by
  rw [ofGen_perm, latTr]
  dsimp only
  refine sum_congr rfl fun i hi => ?_
  rw [permG_getD' arr i i (mem_range.1 hi) (mem_range.1 hi)]

theorem latTr2_perm (arr : Array ℕ) :
    latTr2 (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) =
      ∑ i ∈ range 24, ∑ k ∈ range 24,
        (if arr[i]! = k then 1 else 0) * (if arr[k]! = i then 1 else 0) := by
  rw [ofGen_perm, latTr2]
  dsimp only
  refine sum_congr rfl fun i hi => sum_congr rfl fun k hk => ?_
  rw [permG_getD' arr i k (mem_range.1 hi) (mem_range.1 hk),
    permG_getD' arr k i (mem_range.1 hk) (mem_range.1 hi)]

end Perm

end CFSG.KC.Trace6091

end
