module

public import CFSG.Certificates.Kernel.KDense.SepVec
public import CFSG.Certificates.Kernel.KDense.SortSound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.KDense.SepAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.KDense.InitAux
  CFSG.KC.KDense.P15 CFSG.KC.KDense.TabAux CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371
  CFSG.YGroups.Y443Native


theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem recAllB {P : ℕ → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (P i) ih) n = true →
      ∀ i < n, P i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true' h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact recAllB n h2 i hi
    · exact h1

theorem recAllB2 {P Q : ℕ → Bool} : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (P i) (andB (Q i) ih)) n = true →
      ∀ i < n, P i = true ∧ Q i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true' h
    obtain ⟨h3, h4⟩ := andB_true' h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact recAllB2 n h4 i hi
    · exact ⟨h1, h3⟩

theorem utRange_zero (OCT K lo : ℕ) : utRange OCT 0 K lo = Nat.beq K (svRec OCT lo) := rfl

theorem utRange_succ (OCT e K lo : ℕ) : utRange OCT (e + 1) K lo =
    andB (utRange OCT e (Nat.land K (ones (Nat.mul (nat_lit 128) (Nat.shiftLeft (nat_lit 1) e)))) lo)
      (utRange OCT e (Nat.shiftRight K (Nat.mul (nat_lit 128) (Nat.shiftLeft (nat_lit 1) e)))
        (Nat.add lo (Nat.shiftLeft (nat_lit 1) e))) := rfl

theorem utRange_bits (OCT : ℕ) : ∀ d K lo, utRange OCT d K lo = true →
    ∀ t < 2 ^ d, ∀ j < 128, K.testBit (128 * t + j) = (svRec OCT (lo + t)).testBit j
  | 0, K, lo, h, t, ht, j, _ => by
    rw [utRange_zero] at h
    have := Nat.eq_of_beq_eq_true h
    obtain rfl : t = 0 := by simpa using ht
    rw [this]
    simp
  | e + 1, K, lo, h, t, ht, j, hj => by
    rw [utRange_succ] at h
    obtain ⟨h1, h2⟩ := andB_true' h
    have eh : Nat.shiftLeft (nat_lit 1) e = 2 ^ e := by rw [nshl, Nat.one_shiftLeft]
    rw [eh] at h1 h2
    have e2 : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [Nat.pow_succ]; ring
    rcases Nat.lt_or_ge t (2 ^ e) with h3 | h3
    · have := utRange_bits OCT e _ _ h1 t h3 j hj
      rw [← this, nland, nmul, Nat.testBit_and, SortAux.testBit_ones,
        decide_eq_true (by nlinarith), Bool.and_true]
    · have := utRange_bits OCT e _ _ h2 (t - 2 ^ e) (by omega) j hj
      rw [nshr, nmul, nadd, Nat.testBit_shiftRight, show lo + 2 ^ e + (t - 2 ^ e) = lo + t by omega,
        show 128 * 2 ^ e + (128 * (t - 2 ^ e) + j) = 128 * t + j by
          rw [Nat.mul_sub]
          have : 128 * 2 ^ e ≤ 128 * t := Nat.mul_le_mul_left _ h3
          omega] at this
      exact this

theorem utSlice_bit (UT i r : ℕ) (hr : r < 2097152) :
    (utSlice UT i).testBit r = UT.testBit (i * 2097152 + r) := by
  unfold utSlice
  rw [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, SortAux.testBit_ones,
    decide_eq_true hr, Bool.and_true]

theorem ut_bits {OCT UT : ℕ} (h : utOK OCT UT = true) {p j : ℕ} (hp : p < SX) (hj : j < 128) :
    UT.testBit (128 * p + j) = (svRec OCT p).testBit j := by
  unfold utOK at h
  generalize hN : nat_lit 8 = N at h
  have hN' : N = 8 := hN.symm
  have hS : SX = 131072 := rfl
  have hi := recAllB (P := fun i => utRange OCT (nat_lit 14) (utSlice UT i) (Nat.mul i (nat_lit 16384)))
    N h (p / 16384) (by rw [hN']; rw [hS] at hp; omega)
  have := utRange_bits OCT 14 _ _ hi (p % 16384) (Nat.mod_lt _ (by decide)) j hj
  have e1 : Nat.mul (p / 16384) (nat_lit 16384) + p % 16384 = p := by
    rw [nmul]
    exact Nat.div_add_mod' p 16384
  have e2 : p / 16384 * 2097152 + (128 * (p % 16384) + j) = 128 * p + j := by
    have h0 := Nat.div_add_mod p 16384
    calc p / 16384 * 2097152 + (128 * (p % 16384) + j)
        = 128 * (16384 * (p / 16384) + p % 16384) + j := by ring
      _ = 128 * p + j := by rw [h0]
  have e3 : 128 * (p % 16384) + j < 2097152 := by
    have h0 : p % 16384 < 16384 := Nat.mod_lt _ (by decide)
    have h1 : p % 16384 ≤ 16383 := by omega
    have h2 : 128 * (p % 16384) ≤ 128 * 16383 := Nat.mul_le_mul_left _ h1
    omega
  rw [utSlice_bit _ _ _ e3, e1, e2] at this
  exact this

theorem uFromUT_bit {UT l i p : ℕ} (hi : i < 4) (hp : p < SX) :
    (uFromUT UT l).testBit (i * SX + p) = UT.testBit (128 * p + (4 * l + i)) := by
  have eU : uFromUT UT l = Nat.rec (motive := fun _ => ℕ) 0 (fun b acc => Nat.lor acc
      (Nat.shiftLeft (rawPlane UT 128 SX 17 0 (4 * l + b)) (b * SX))) 4 := rfl
  have hS : SX = 131072 := rfl
  rw [eU, Bool.eq_iff_iff, testBit_foldOr]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, InitAux.testBit_shl,
    SortAux.testBit_rawPlane (by decide : 0 < 128) SortAux.SX_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨b, hb, h1, h2, h3⟩
    rw [hS] at h1 h2 hp
    obtain rfl : b = i := by omega
    rw [Nat.add_sub_cancel_left] at h3
    exact h3
  · intro h
    refine ⟨i, by omega, Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hp, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact h

theorem uVec_bit {UT U l i p : ℕ} (h : uPlanesOK UT U = true) (hl : l < 24) (hi : i < 4)
    (hp : p < SX) : (uVec U l).testBit (i * SX + p) = UT.testBit (128 * p + (4 * l + i)) := by
  unfold uPlanesOK at h
  obtain ⟨-, h2⟩ := andB_true' h
  generalize hN : nat_lit 24 = N at h2
  have := Nat.eq_of_beq_eq_true (recAllB (P := fun l => Nat.beq (uVec U l) (uFromUT UT l)) N h2 l
    (by rw [← hN]; exact hl))
  rw [this, uFromUT_bit hi hp]

theorem resP_uVec {OCT UT U : ℕ} (h1 : octOK OCT = true)
    (h2 : utOK OCT UT = true) (h3 : uPlanesOK UT U = true) {q l : ℕ} (hq : q < 98280)
    (hl : l < 24) : resP SX (uVec U l) (xposK q) = (((shortVecN q)[l]! : ℤ) : ZMod 15) := by
  obtain ⟨v, hv, hb, hc⟩ := svRec_entry h1 hq hl
  have hp := xposK_lt' hq
  rw [resP_dg, ← hc]
  refine congrArg _ (dg_ext (dg_lt _ _ _) hv fun i hi => ?_)
  rw [testBit_dg, decide_eq_true hi, Bool.true_and, uVec_bit h3 hl hi hp,
    ut_bits h2 hp (by omega), hb i hi]

@[expose] def apow (tab : Array ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0, i, j => if i = j then 1 else 0
  | k + 1, i, j => ∑ m ∈ Finset.range 24, apow tab k i m * tab[Native.aIdx m j]!

theorem rec_sum (f : ℕ → ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun m acc => Nat.add acc (f m)) n =
      ∑ m ∈ Finset.range n, f m
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← rec_sum f n]
    rfl

theorem tabList (tab : Array ℤ) : Array.rec (motive := fun _ => List Int) (fun l => l) tab =
    tab.toList := by
  cases tab
  rfl

theorem mEnt_pow {tab : Array ℤ} {MK : ℕ} (h : mkOK tab MK = true) :
    ∀ k ≤ 14, ∀ i < 24, ∀ j < 24, (mEnt MK k i j : ZMod 15) = (apow tab k i j : ZMod 15) := by
  unfold mkOK at h
  rw [tabList] at h
  beta_reduce at h
  obtain ⟨-, h⟩ := andB_true' h
  generalize hN : nat_lit 24 = N at h
  generalize hM : nat_lit 14 = M at h
  rw [← hN, ← hM]
  have hN' : N = 24 := hN.symm
  have hM' : M = 14 := hM.symm
  have hi := recAllB N h
  have hij := fun i (hi' : i < 24) j (hj : j < 24) =>
    recAllB2 N (hi i (by rw [hN']; exact hi')) j (by rw [hN']; exact hj)
  intro k
  induction k with
  | zero =>
    intro _ i hi' j hj
    have h0 := Nat.eq_of_beq_eq_true (hij i hi' j hj).1
    rw [h0, apow]
    by_cases e : i = j
    · subst e
      have : Nat.beq i i = true := Nat.beq_refl i
      rw [this, ite_eq_left rfl]
      rfl
    · have : Nat.beq i j = false := by
        cases hc : Nat.beq i j
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hc) e
      rw [this, ite_eq_right e]
      rfl
  | succ k ih =>
    intro hk i hi' j hj
    have h1 := recAllB M (hij i hi' j hj).2 k (by rw [hM']; omega)
    have h1' := Nat.eq_of_beq_eq_true h1
    rw [hN'] at h1'
    simp only [nmod] at h1'
    rw [h1', rec_sum, ZMod.natCast_mod, apow]
    push_cast
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    rw [nmul, Nat.cast_mul, ih (by omega) i hi' m hm', res15I_cast, lgetI_toList,
      aIdxT_eq m hm' j hj]

end CFSG.KC.KDense.SepAux

end
