module

public import CFSG.Certificates.Kernel.YModel.NetSem
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Bound.Init
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.LawfulXor.Basic
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.YModel.Sch

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.YModel CFSG.KC.YModel.Sem

@[expose] def Good (k n N : Nat) : Prop :=
  n ≤ 2 ^ k ∧ StagesValid k N ∧ ∀ i, n ≤ i → i < 2 ^ k → benesPerm k N i = i

theorem Good.lt {k n N i : Nat} (h : Good k n N) (hi : i < n) : benesPerm k N i < n :=
  perm_lt h.1 h.2.1 h.2.2 hi

theorem Good.inv_lt {k n N i : Nat} (h : Good k n N) (hi : i < n) : benesInv k N i < n := by
  by_contra hc
  have h1 := benesInv_lt h.2.1 (show i < 2 ^ k by have := h.1; omega)
  have := h.2.2 _ (by omega) h1
  rw [benesPerm_benesInv h.2.1] at this
  omega

noncomputable def netPerm (k n N : Nat) : Equiv.Perm (Fin n) := by
  classical
  exact if h : Good k n N then
    { toFun := fun i => ⟨benesPerm k N i, h.lt i.2⟩
      invFun := fun i => ⟨benesInv k N i, h.inv_lt i.2⟩
      left_inv := fun i => Fin.ext (benesInv_benesPerm h.2.1 i)
      right_inv := fun i => Fin.ext (benesPerm_benesInv h.2.1 i) }
  else 1

theorem netPerm_apply {k n N : Nat} (h : Good k n N) (i : Fin n) :
    (netPerm k n N i : Nat) = benesPerm k N i := by
  unfold netPerm
  rw [dif_pos h]
  rfl

theorem prod_apply {k n : Nat} : ∀ Ns : List Nat, (∀ N ∈ Ns, Good k n N) → ∀ i : Fin n,
    (((Ns.map (netPerm k n)).prod i : Fin n) : Nat) = compN k Ns i
  | [], _, _ => rfl
  | N :: Ns, h, i => by
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, netPerm_apply (h N List.mem_cons_self),
      prod_apply Ns (fun N' hN' => h N' (List.mem_cons_of_mem _ hN')) i]
    rfl

theorem compN_fix {k n : Nat} : ∀ Ns : List Nat, (∀ N ∈ Ns, Good k n N) →
    ∀ i, n ≤ i → i < 2 ^ k → compN k Ns i = i
  | [], _, _, _, _ => rfl
  | N :: Ns, h, i, h1, h2 => by
    change benesPerm k N (compN k Ns i) = i
    rw [compN_fix Ns (fun N' hN' => h N' (List.mem_cons_of_mem _ hN')) i h1 h2,
      (h N List.mem_cons_self).2.2 i h1 h2]

theorem prod_eq_of {k n : Nat} (hn : n ≤ 2 ^ k) {Ns Ms : List Nat} (h1 : ∀ N ∈ Ns, Good k n N)
    (h2 : ∀ N ∈ Ms, Good k n N) (h : ∀ r < 2 ^ k, compN k Ns r = compN k Ms r) :
    (Ns.map (netPerm k n)).prod = (Ms.map (netPerm k n)).prod := by
  ext i
  rw [prod_apply Ns h1, prod_apply Ms h2, h i (by have := i.2; omega)]

theorem blt_false' {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr fun h' => h (Nat.blt_eq.mp h')

theorem testBit_ones' (W q : Nat) : (ones W).testBit q = decide (q < W) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

theorem stBit_eq (k i : Nat) : KDense.stBit k i = if i < k then k - 1 - i else i + 1 - k := by
  unfold KDense.stBit
  by_cases h : i < k
  · rw [Nat.blt_eq.mpr h, if_pos h]
    rfl
  · rw [blt_false' h, if_neg h]
    rfl

theorem stageShift_rev {k i : Nat} (hi : i < 2 * k - 1) :
    stageShift k i = stageShift k (2 * k - 1 - 1 - i) := by
  rw [stageShift_eq, stageShift_eq, stBit_eq, stBit_eq]
  congr 1
  split_ifs <;> omega

theorem testBit_orRec (f : Nat → Nat) (q : Nat) : ∀ c,
    (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (f i)) c).testBit q = true ↔
      ∃ i < c, (f i).testBit q = true
  | 0 => by
    change Nat.testBit 0 q = true ↔ _
    simp
  | c + 1 => by
    change (Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (f i)) c)
      (f c)).testBit q = true ↔ _
    rw [nlor, Nat.testBit_or, Bool.or_eq_true, testBit_orRec f q c]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨c, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem testBit_benesMask {k N i r : Nat} :
    (benesMask k N i).testBit r = (decide (r < 2 ^ k) && N.testBit (i * 2 ^ k + r)) := by
  unfold benesMask
  rw [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones', Bool.and_comm]

theorem block_eq {W i j r : Nat} (h1 : j * W ≤ i * W + r) (h2 : i * W + r - j * W < W)
    (hr : r < W) : j = i := by
  rcases Nat.lt_trichotomy j i with h | h | h
  · have : (j + 1) * W ≤ i * W := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega
  · exact h
  · have : (i + 1) * W ≤ j * W := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega

theorem benesMask_netRev {k N i : Nat} (hi : i < 2 * k - 1) :
    benesMask k (netRev k N) i = benesMask k N (2 * k - 1 - 1 - i) := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_benesMask, testBit_benesMask]
  by_cases hr : r < 2 ^ k
  · rw [decide_eq_true hr, Bool.true_and, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    unfold netRev
    rw [wid_eq, testBit_orRec]
    simp only [nshl, nland, nshr, nmul, nsub, Nat.testBit_shiftLeft, Bool.and_eq_true,
      decide_eq_true_eq, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones']
    constructor
    · rintro ⟨i', hi', h1, h3, h2⟩
      have e := block_eq h1 h2 hr
      have hi'' : i' = 2 * k - 1 - 1 - i := by omega
      subst hi''
      rw [e, show i * 2 ^ k + r - i * 2 ^ k = r by omega, Nat.add_comm] at h3
      rwa [Nat.add_comm]
    · intro h
      refine ⟨2 * k - 1 - 1 - i, by omega, ?_⟩
      rw [show 2 * k - 2 - (2 * k - 1 - 1 - i) = i by omega,
        show i * 2 ^ k + r - i * 2 ^ k = r by omega]
      exact ⟨by omega, by simpa only [Nat.add_comm] using h, hr⟩
  · rw [decide_eq_false hr, Bool.false_and, Bool.false_and]

theorem stagesValid_netRev {k N : Nat} (h : StagesValid k N) : StagesValid k (netRev k N) := by
  intro i hi
  rw [stageShift_rev hi, benesMask_netRev hi]
  exact h _ (by omega)

theorem benesPerm_netRev {k N : Nat} (r : Nat) : benesPerm k (netRev k N) r = benesInv k N r := by
  unfold benesPerm benesInv
  apply compF_congr 0 (2 * k - 1)
  intro i _ hi
  rw [stageShift_rev (by omega : i < 2 * k - 1), benesMask_netRev (by omega : i < 2 * k - 1)]

theorem Good.netRev {k n N : Nat} (h : Good k n N) : Good k n (netRev k N) := by
  refine ⟨h.1, stagesValid_netRev h.2.1, fun i h1 h2 => ?_⟩
  rw [benesPerm_netRev]
  have := congrArg (benesInv k N) (h.2.2 i h1 h2)
  rw [benesInv_benesPerm h.2.1] at this
  exact this.symm

theorem netPerm_netRev {k n N : Nat} (h : Good k n N) :
    netPerm k n (netRev k N) = (netPerm k n N)⁻¹ := by
  ext i
  rw [netPerm_apply h.netRev, benesPerm_netRev, Equiv.Perm.inv_def]
  have hy : netPerm k n N ((netPerm k n N).symm i) = i := Equiv.apply_symm_apply _ _
  have := congrArg Fin.val hy
  rw [netPerm_apply h] at this
  rw [← this, benesInv_benesPerm h.2.1]

@[expose] noncomputable def codesL (w P len : Nat) : List Nat := (List.range len).map (fieldAt w P)

theorem fieldAt_shr (w P i : Nat) : fieldAt w (P >>> w) i = fieldAt w P (i + 1) := by
  rw [fieldAt_eq', fieldAt_eq', ← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]

theorem codesL_succ (w P len : Nat) :
    codesL w P (len + 1) = fieldAt w P 0 :: codesL w (P >>> w) len := by
  unfold codesL
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, fieldAt_shr]

theorem wordNets_eq (k w : Nat) (T : Nat → Nat) : ∀ len P,
    wordNets k w T P len = (codesL w P len).map (codeNet k T)
  | 0, _ => rfl
  | len + 1, P => by
    change codeNet k T (fieldAt w P 0) :: wordNets k w T (Nat.shiftRight P w) len = _
    rw [wordNets_eq k w T len, codesL_succ, List.map_cons]
    rfl

theorem codesIn_spec {w lo hi : Nat} : ∀ len P, codesIn w lo hi P len = true →
    ∀ x ∈ codesL w P len, lo < x >>> 1 ∧ x >>> 1 ≤ hi
  | 0, _, _, x, hx => by simp [codesL] at hx
  | len + 1, P, h, x, hx => by
    change andB (Nat.blt lo (Nat.shiftRight (fieldAt w P 0) 1))
      (andB (Nat.ble (Nat.shiftRight (fieldAt w P 0) 1) hi) (codesIn w lo hi (Nat.shiftRight P w) len))
      = true at h
    obtain ⟨h1, h2⟩ := andB_eq h
    obtain ⟨h2, h3⟩ := andB_eq h2
    rw [codesL_succ] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨Nat.blt_eq.mp h1, Nat.le_of_ble_eq_true h2⟩
    · exact codesIn_spec len _ h3 x hx

theorem fieldAt_lt (w P i : Nat) : fieldAt w P i < 2 ^ w := by
  rw [fieldAt_eq']
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem mem_codesL_lt {w P len x : Nat} (h : x ∈ codesL w P len) : x < 2 ^ w := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  exact fieldAt_lt w P i

theorem fieldAt_or_shl {w A B L i : Nat} (hA : A < 2 ^ (w * L)) :
    fieldAt w (A ||| (B <<< (w * L))) i = if i < L then fieldAt w A i else fieldAt w B (i - L) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_fieldAt, Nat.testBit_or, Nat.testBit_shiftLeft]
  split_ifs with hi
  · rw [testBit_fieldAt]
    by_cases hj : j < w
    · have : ¬ w * i + j ≥ w * L := by
        have : w * i + w ≤ w * L := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
        omega
      rw [decide_eq_false this, Bool.false_and, Bool.or_false]
    · rw [decide_eq_false hj, Bool.false_and, Bool.false_and]
  · rw [testBit_fieldAt]
    by_cases hj : j < w
    · have h1 : w * L ≤ w * i := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.testBit_lt_two_pow (lt_two_pow_mono hA (by omega)), Bool.false_or,
        decide_eq_true (show w * i + j ≥ w * L by omega), decide_eq_true hj,
        show w * i + j - w * L = w * (i - L) + j by rw [Nat.mul_sub]; omega, Bool.true_and]
    · rw [decide_eq_false hj, Bool.false_and, Bool.false_and]

theorem codesL_catW {w P1 L1 P2 L2 : Nat} (h : P1 < 2 ^ (w * L1)) :
    codesL w (catW w P1 L1 P2) (L1 + L2) = codesL w P1 L1 ++ codesL w P2 L2 := by
  have e : catW w P1 L1 P2 = P1 ||| (P2 <<< (w * L1)) := by
    unfold catW
    rw [nlor, nshl, nmul]
  unfold codesL
  rw [List.range_add, List.map_append, List.map_map, e]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [fieldAt_or_shl h, if_pos (List.mem_range.mp hi)]
  · apply List.map_congr_left
    intro i _
    rw [Function.comp_apply, fieldAt_or_shl h, if_neg (by omega), Nat.add_sub_cancel_left]

theorem fieldAt_push {w acc g : Nat} (hg : g < 2 ^ w) (i : Nat) :
    fieldAt w ((acc <<< w) ||| g) i = if i = 0 then g else fieldAt w acc (i - 1) := by
  have e : (acc <<< w) ||| g = g ||| (acc <<< (w * 1)) := by rw [Nat.or_comm, Nat.mul_one]
  rw [e, fieldAt_or_shl (L := 1) (by rwa [Nat.mul_one])]
  by_cases hi : i = 0
  · subst hi
    rw [if_pos (by decide), if_pos rfl, fieldAt_eq', Nat.mul_zero, Nat.shiftRight_zero,
      Nat.mod_eq_of_lt hg]
  · rw [if_neg (by omega), if_neg hi]

theorem invA_spec {w : Nat} (hw : 0 < w) : ∀ (len Q acc a : Nat), acc < 2 ^ (w * a) →
    (∀ i, fieldAt w (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun _ ih Q acc => ih (Nat.shiftRight Q w)
        (Nat.lor (Nat.shiftLeft acc w)
          (Nat.xor (Nat.land Q (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))) (nat_lit 1))))
      len Q acc) i =
        if i < len then fieldAt w Q (len - 1 - i) ^^^ 1 else fieldAt w acc (i - len)) ∧
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun _ ih Q acc => ih (Nat.shiftRight Q w)
        (Nat.lor (Nat.shiftLeft acc w)
          (Nat.xor (Nat.land Q (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))) (nat_lit 1))))
      len Q acc < 2 ^ (w * (a + len))
  | 0, Q, acc, a, h => ⟨fun i => by simp, by simpa using h⟩
  | len + 1, Q, acc, a, h => by
    have hg : fieldAt w Q 0 ^^^ 1 < 2 ^ w :=
      Nat.xor_lt_two_pow (fieldAt_lt w Q 0) (Nat.one_lt_two_pow (by omega))
    have hacc : (acc <<< w) ||| (fieldAt w Q 0 ^^^ 1) < 2 ^ (w * (a + 1)) := by
      apply Nat.or_lt_two_pow _ (lt_two_pow_mono hg (by rw [Nat.mul_succ]; omega))
      rw [Nat.shiftLeft_eq, Nat.mul_succ, Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)
    obtain ⟨ih1, ih2⟩ := invA_spec hw len (Q >>> w) _ (a + 1) hacc
    refine ⟨fun i => ?_, by rw [show a + (len + 1) = a + 1 + len by omega]; exact ih2⟩
    change fieldAt w (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
      (fun _ ih Q acc => ih (Nat.shiftRight Q w)
        (Nat.lor (Nat.shiftLeft acc w)
          (Nat.xor (Nat.land Q (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))) (nat_lit 1))))
      len (Q >>> w) ((acc <<< w) ||| (fieldAt w Q 0 ^^^ 1))) i = _
    rw [ih1 i, fieldAt_push hg]
    by_cases h1 : i < len
    · rw [if_pos h1, if_pos (by omega), fieldAt_shr, show len - 1 - i + 1 = len + 1 - 1 - i by omega]
    · rw [if_neg h1]
      by_cases h2 : i = len
      · subst h2
        rw [if_pos (by omega), if_pos (by omega), show i + 1 - 1 - i = 0 by omega]
      · rw [if_neg (by omega), if_neg (by omega), show i - len - 1 = i - (len + 1) by omega]

theorem codesL_invW {w P len : Nat} (hw : 0 < w) :
    codesL w (invW w P len) len = ((codesL w P len).reverse).map (· ^^^ 1) ∧
      invW w P len < 2 ^ (w * len) := by
  obtain ⟨h1, h2⟩ := invA_spec hw len P 0 0 (by simp)
  refine ⟨?_, by rw [Nat.zero_add] at h2; exact h2⟩
  apply List.ext_getElem
  · simp [codesL]
  · intro i hi1 hi2
    simp only [codesL, List.length_map, List.length_range] at hi1
    simp only [codesL, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_map, List.length_range]
    exact (h1 i).trans (if_pos hi1)

section Words

variable (k n w : Nat) (U : Nat → Nat)

@[expose] noncomputable def cperm (x : Nat) : Equiv.Perm (Fin n) :=
  if x.testBit 0 then (netPerm k n (U ((x >>> 1) - 1)))⁻¹ else netPerm k n (U ((x >>> 1) - 1))

@[expose] noncomputable def cpermL (cs : List Nat) : Equiv.Perm (Fin n) := (cs.map (cperm k n U)).prod

end Words

theorem bitB_zero (x : Nat) : bitB x 0 = x.testBit 0 := by
  unfold bitB
  change ((x &&& 1) == 1) = _
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem codeNet_eq {k : Nat} {T : Nat → Nat} (x : Nat) :
    codeNet k T x = if x.testBit 0 then netRev k (T ((x >>> 1) - 1)) else T ((x >>> 1) - 1) := by
  unfold codeNet
  rw [bitB_zero]
  cases x.testBit 0 <;> rfl

theorem good_codeNet {k n x : Nat} {U : Nat → Nat} (h : Good k n (U ((x >>> 1) - 1))) :
    Good k n (codeNet k U x) := by
  rw [codeNet_eq]
  split
  · exact h.netRev
  · exact h

theorem netPerm_codeNet {k n x : Nat} {U : Nat → Nat} (h : Good k n (U ((x >>> 1) - 1))) :
    netPerm k n (codeNet k U x) = cperm k n U x := by
  rw [codeNet_eq, cperm]
  split
  · exact netPerm_netRev h
  · rfl

@[expose] def CodesGood (k n : Nat) (U : Nat → Nat) (cs : List Nat) : Prop :=
  ∀ x ∈ cs, Good k n (U ((x >>> 1) - 1))

theorem good_wordNets {k n w P len : Nat} {U : Nat → Nat} (h : CodesGood k n U (codesL w P len)) :
    ∀ N ∈ wordNets k w U P len, Good k n N := by
  rw [wordNets_eq]
  intro N hN
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hN
  exact good_codeNet (h x hx)

theorem prod_wordNets {k n w P len : Nat} {U : Nat → Nat} (h : CodesGood k n U (codesL w P len)) :
    ((wordNets k w U P len).map (netPerm k n)).prod = cpermL k n U (codesL w P len) := by
  rw [wordNets_eq, List.map_map, cpermL]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact netPerm_codeNet (h x hx)

theorem cperm_xor {k n : Nat} {U : Nat → Nat} (x : Nat) :
    cperm k n U (x ^^^ 1) = (cperm k n U x)⁻¹ := by
  have h1 : (x ^^^ 1) >>> 1 = x >>> 1 := by
    rw [Nat.shiftRight_xor_distrib]
    simp
  have h2 : (x ^^^ 1).testBit 0 = !x.testBit 0 := by
    rw [Nat.testBit_xor]
    simp
  unfold cperm
  rw [h1, h2]
  cases x.testBit 0 <;> simp

theorem cpermL_inv {k n : Nat} {U : Nat → Nat} (cs : List Nat) :
    cpermL k n U ((cs.reverse).map (· ^^^ 1)) = (cpermL k n U cs)⁻¹ := by
  unfold cpermL
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse, List.map_map]
  congr 2
  apply List.map_congr_left
  intro x _
  exact cperm_xor x

theorem cpermL_append {k n : Nat} {U : Nat → Nat} (a b : List Nat) :
    cpermL k n U (a ++ b) = cpermL k n U a * cpermL k n U b := by
  unfold cpermL
  rw [List.map_append, List.prod_append]

theorem cpermL_mem {k n : Nat} {U : Nat → Nat} {H : Subgroup (Equiv.Perm (Fin n))} :
    ∀ cs : List Nat, (∀ x ∈ cs, netPerm k n (U ((x >>> 1) - 1)) ∈ H) → cpermL k n U cs ∈ H
  | [], _ => H.one_mem
  | x :: cs, h => by
    unfold cpermL
    rw [List.map_cons, List.prod_cons]
    refine H.mul_mem ?_ (cpermL_mem cs fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold cperm
    split
    · exact H.inv_mem (h x List.mem_cons_self)
    · exact h x List.mem_cons_self

theorem sweqK_spec {k n w P1 L1 P2 L2 : Nat} {U : Nat → Nat} (hn : n ≤ 2 ^ k)
    (h1 : CodesGood k n U (codesL w P1 L1)) (h2 : CodesGood k n U (codesL w P2 L2))
    (h : sweqK k w U P1 L1 P2 L2 = true) :
    cpermL k n U (codesL w P1 L1) = cpermL k n U (codesL w P2 L2) := by
  have g1 := good_wordNets h1
  have g2 := good_wordNets h2
  rw [← prod_wordNets h1, ← prod_wordNets h2]
  apply prod_eq_of hn g1 g2
  have e := Nat.eq_of_beq_eq_true h
  rw [wid_eq] at e
  exact eq_of_idP (acts_netsApply _ fun N hN => (g1 N hN).2.1)
    (acts_netsApply _ fun N hN => (g2 N hN).2.1) e

theorem mapsTo_spec {k n w P len b x : Nat} {U : Nat → Nat} (hn : n ≤ 2 ^ k) (hb : b < n)
    (h1 : CodesGood k n U (codesL w P len)) (h : mapsTo k w U P len b x = true) :
    ((cpermL k n U (codesL w P len) ⟨b, hb⟩ : Fin n) : Nat) = x := by
  have g1 := good_wordNets h1
  rw [← prod_wordNets h1, prod_apply _ g1]
  have e := Nat.eq_of_beq_eq_true h
  rw [wid_eq] at e
  have e' : netsApply k (2 ^ k) (repU (2 ^ k) 1) (wordNets k w U P len) (Nat.shiftLeft 1 x) =
      Nat.shiftLeft 1 b := by
    rw [← repU_one' k]
    exact e
  exact eq_of_point (acts_netsApply _ fun N hN => (g1 N hN).2.1) (by omega) e'

end CFSG.KC.YModel.Sch

end
