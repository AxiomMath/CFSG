module

public import Certificates.Data.CFSGNative.F3.Conj
public import CFSG.F3.Spec
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.F3.Native

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem idM_size' (d : ℕ) : (idM d).size = d := by unfold Native.idM; simp


theorem V.canon_testBit {d : ℕ} {a : V} (h : a.wf && a.p >>> d == 0 && a.m >>> d == 0)
    {j : ℕ} (hj : d ≤ j) : a.p.testBit j = false ∧ a.m.testBit j = false := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, hp⟩, hm⟩ := h
  have hp' : a.p < 2 ^ d := by
    rw [Nat.shiftRight_eq_div_pow] at hp
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos d)).1 hp
  have hm' : a.m < 2 ^ d := by
    rw [Nat.shiftRight_eq_div_pow] at hm
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos d)).1 hm
  exact ⟨Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hp' (Nat.pow_le_pow_right (by norm_num) hj)),
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by norm_num) hj))⟩

private theorem bitVal_inj : ∀ p m p' m' : Bool, (p && m) = false → (p' && m') = false →
    bitVal p m = bitVal p' m' → p = p' ∧ m = m' := by
  decide

theorem V.eq_of_canon {d : ℕ} {a b : V} (ha : a.wf && a.p >>> d == 0 && a.m >>> d == 0)
    (hb : b.wf && b.p >>> d == 0 && b.m >>> d == 0) (h : ∀ j < d, a.val j = b.val j) :
    a = b := by
  have hwa : a.wf = true := by simp only [Bool.and_eq_true] at ha; exact ha.1.1
  have hwb : b.wf = true := by simp only [Bool.and_eq_true] at hb; exact hb.1.1
  have hbits : ∀ j, a.p.testBit j = b.p.testBit j ∧ a.m.testBit j = b.m.testBit j := by
    intro j
    by_cases hj : j < d
    · have := h j hj
      rw [V.val_eq_bitVal, V.val_eq_bitVal] at this
      exact bitVal_inj _ _ _ _ (V.not_both hwa j) (V.not_both hwb j) this
    · obtain ⟨h1, h2⟩ := V.canon_testBit ha (by omega : d ≤ j)
      obtain ⟨h3, h4⟩ := V.canon_testBit hb (by omega : d ≤ j)
      rw [h1, h2, h3, h4]
      exact ⟨rfl, rfl⟩
  cases a
  cases b
  simp only [V.mk.injEq]
  exact ⟨Nat.eq_of_testBit_eq fun j => (hbits j).1, Nat.eq_of_testBit_eq fun j => (hbits j).2⟩

theorem canonM_spec {d : ℕ} {X : Array V} (h : canonM d X = true) :
    X.size = d ∧ ∀ i < X.size, (X[i]!.wf && X[i]!.p >>> d == 0 && X[i]!.m >>> d == 0) = true := by
  unfold canonM at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  refine ⟨h.1, fun i hi => ?_⟩
  rw [getElem!_pos X i hi]
  have := h.2 i hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this ⊢
  exact this

theorem RowsWF.of_canonM {d : ℕ} {X : Array V} (h : canonM d X = true) : RowsWF X := by
  obtain ⟨-, hX⟩ := canonM_spec h
  intro j
  by_cases hj : j < X.size
  · have := hX j hj
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  · rw [getElem!_neg X j hj]; exact V.wf_zero

theorem eq_of_canonM {d : ℕ} {X Y : Array V} (hX : canonM d X = true) (hY : canonM d Y = true)
    (h : toMat d X = toMat d Y) : X = Y := by
  obtain ⟨hXs, hX'⟩ := canonM_spec hX
  obtain ⟨hYs, hY'⟩ := canonM_spec hY
  apply Array.ext (by rw [hXs, hYs])
  intro i hi hi'
  have e := V.eq_of_canon (d := d) (hX' i hi) (hY' i hi') (fun j hj => by
    have := congrFun (congrFun h ⟨i, by rw [← hXs]; exact hi⟩) ⟨j, hj⟩
    rwa [toMat_apply, toMat_apply] at this)
  rwa [getElem!_pos X i hi, getElem!_pos Y i hi'] at e

theorem canonM_idM (d : ℕ) : canonM d (idM d) = true := by
  unfold canonM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨idM_size' d, fun i hi => ?_⟩
  have hi' : i < d := by rwa [idM_size'] at hi
  simp only [Native.idM, Array.getElem_ofFn]
  have hw : (⟨1 <<< i, 0⟩ : V).wf = true := by
    apply V.wf_of_bits; intro j; simp
  simp only [hw, Bool.true_and, beq_iff_eq, Bool.and_eq_true]
  refine ⟨?_, by simp⟩
  rw [Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft]
  exact Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi')

theorem conjM_size {d : ℕ} {g gi X : Array V} (hg : g.size = d) : (conjM d g gi X).size = d := by
  unfold conjM Native.mul
  rw [Array.size_map, Array.size_map, hg]

theorem RowsWF.conjM {d : ℕ} {g gi X : Array V} (hg : RowsWF g) (hgi : RowsWF gi) (hX : RowsWF X) :
    RowsWF (conjM d g gi X) :=
  RowsWF.mul _ d (RowsWF.mul _ d hg hX) hgi

theorem toMat_conjM {d : ℕ} {g gi X : Array V} (hgs : g.size = d) (hg : RowsWF g)
    (hgi : RowsWF gi) (hX : RowsWF X) :
    toMat d (conjM d g gi X) = toMat d g * toMat d X * toMat d gi := by
  unfold conjM
  have hs : (mul d g X).size = d := by unfold Native.mul; rw [Array.size_map, hgs]
  rw [toMat_mul hs (RowsWF.mul _ d hg hX) hgi, toMat_mul hgs hg hX]

structure ConjFacts (d : ℕ) (A Ai B Bi : Array V) (O : COrbit) : Prop where
  size_pos : 0 < O.keys.size
  size_lt : O.keys.size < 2 ^ 32
  canon : ∀ k < O.keys.size, canonM d O.keys[k]! = true
  alpha : ∀ k < O.keys.size, ap O.alpha k < O.keys.size ∧
    toMat d O.keys[ap O.alpha k]! = toMat d A * toMat d O.keys[k]! * toMat d Ai
  beta : ∀ k < O.keys.size, ap O.beta k < O.keys.size ∧
    toMat d O.keys[ap O.beta k]! = toMat d B * toMat d O.keys[k]! * toMat d Bi
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, toMat d O.keys[i]! = toMat d O.keys[j]! → i = j
  tree : ∀ k < O.keys.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))
  root : toMat d O.keys[0]! = toMat d A

theorem conjOrbitOK_facts {d : ℕ} {A Ai B Bi : Array V} {O : COrbit} {c : ℕ}
    (hAs : A.size = d) (hA : RowsWF A) (hAi : RowsWF Ai) (hBs : B.size = d) (hB : RowsWF B)
    (hBi : RowsWF Bi) (h : conjOrbitOK d A Ai B Bi O c = true) : ConjFacts d A Ai B Bi O := by
  unfold conjOrbitOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hpos, hlt⟩, hroot⟩, hall⟩ := h
  set pos : Array V → ℕ := fun X => (indexOf O.keys).getD (keyOf X) O.keys.size
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.keys.size, canonM d O.keys[k]! = true ∧ pos O.keys[k]! = k ∧
      ap O.alpha k < O.keys.size ∧ eqM d (conjM d A Ai O.keys[k]!) O.keys[ap O.alpha k]! = true ∧
      ap O.beta k < O.keys.size ∧ eqM d (conjM d B Bi O.keys[k]!) O.keys[ap O.beta k]! = true ∧
      (k = 0 ∨ (ap O.par k < k ∧ ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨
        (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k)))) := by
    intro k hk
    have := hat k hk
    simp only [conjCheckAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
      at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨hpos, hlt, fun k hk' => (hk k hk').1, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk'
    obtain ⟨hc, -, ha, he, -⟩ := hk k hk'
    refine ⟨ha, ?_⟩
    rw [← toMat_eq_of_eqM he, toMat_conjM hAs hA hAi (RowsWF.of_canonM hc)]
  · intro k hk'
    obtain ⟨hc, -, -, -, hb, he, -⟩ := hk k hk'
    refine ⟨hb, ?_⟩
    rw [← toMat_eq_of_eqM he, toMat_conjM hBs hB hBi (RowsWF.of_canonM hc)]
  · intro i hi j hj hij
    have e := eq_of_canonM (hk i hi).1 (hk j hj).1 hij
    rw [← (hk i hi).2.1, ← (hk j hj).2.1, e]
  · intro k hk' hk0
    rcases (hk k hk').2.2.2.2.2.2 with h0 | h1
    · omega
    · exact h1
  · exact toMat_eq_of_eqM hroot

end CFSG.F3.Native
