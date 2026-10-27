module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3Sound
public import Certificates.Data.Kernel.G2Three.Sec1T3A
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Monotonicity.Lemmas
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

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem lstM_bit (k : ℕ) : ∀ l : List ℕ, (lstM l).testBit k = true ↔ k ∈ l
  | [] => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | x :: l => by
    change (1 <<< x ||| lstM l).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, lstM_bit k l, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_eq, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

theorem stepK_bit (C M k : ℕ) : ∀ gs : List ℕ, (stepK C gs M).testBit k = true ↔
    M.testBit k = true ∨ ∃ g ∈ gs, (imgR (rowT C g) M).testBit k = true
  | [] => by
    change M.testBit k = true ↔ _
    simp
  | g :: gs => by
    change (stepK C gs M ||| imgR (rowT C g) M).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, stepK_bit C M k gs]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)

theorem recLorIf_bit (c : ℕ → Bool) (F : ℕ → ℕ) (k : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) 0 (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n).testBit
      k = true ↔ ∃ b < n, c b = true ∧ (F b).testBit k = true
  | 0 => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | n + 1 => by
    have ih := recLorIf_bit c F k n
    change (nIf(c n, Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n) (F n),
      Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n)).testBit k = true ↔ _
    generalize Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => nIf(c b, Nat.lor acc (F b), acc)) n = R at ih ⊢
    cases hc : c n
    · change R.testBit k = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨b, hb, h1, h2⟩
        exact ⟨b, Nat.lt_succ_of_lt hb, h1, h2⟩
      · rintro ⟨b, hb, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · exact ⟨b, hb, h1, h2⟩
        · rw [hc] at h1
          exact absurd h1 (by decide)
    · change (R ||| F n).testBit k = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨b, hb, h1, h2⟩ | h)
        · exact ⟨b, Nat.lt_succ_of_lt hb, h1, h2⟩
        · exact ⟨n, Nat.lt_succ_self n, hc, h⟩
      · rintro ⟨b, hb, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb | rfl
        · exact Or.inl ⟨b, hb, h1, h2⟩
        · exact Or.inr h2

variable {G : Type} [Group G] {elt : ℕ → G}

theorem mset_recMask (c : ℕ → Bool) (g : ℕ → ℕ) (hg : ∀ i < 128, g i < 128) :
    mset elt (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.lor acc (Nat.shiftLeft 1 (g i)), acc)) 128) =
      {x | ∃ i < 128, c i = true ∧ elt (g i) = x} := by
  have hb : ∀ k, hasB (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.lor acc (Nat.shiftLeft 1 (g i)), acc)) 128) k = true ↔
      ∃ i < 128, c i = true ∧ g i = k := fun k => by
    rw [hasB_eq]
    exact recMask_bit c g k 128
  ext x
  constructor
  · rintro ⟨k, -, hk, rfl⟩
    obtain ⟨i, hi, hc, rfl⟩ := (hb _).1 hk
    exact ⟨i, hi, hc, rfl⟩
  · rintro ⟨i, hi, hc, rfl⟩
    exact ⟨g i, hg i hi, (hb _).2 ⟨i, hi, hc, rfl⟩, rfl⟩

theorem mset_recMaskId (c : ℕ → Bool) :
    mset elt (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128) =
      {x | ∃ i < 128, c i = true ∧ elt i = x} :=
  mset_recMask c (fun i => i) fun _ hi => hi

theorem mset_one (h1 : elt 0 = 1) : mset elt 1 = {1} := by
  ext g
  simp only [mset, Set.mem_setOf_eq, Set.mem_singleton_iff, hasB_eq,
    Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · rintro ⟨i, -, rfl, rfl⟩
    exact h1
  · rintro rfl
    exact ⟨0, by decide, rfl, h1⟩

theorem lstM_mset {l : List ℕ} (hl : ∀ x ∈ l, x < 128) :
    mset elt (lstM l) = {g | ∃ x ∈ l, elt x = g} := by
  ext g
  simp only [mset, Set.mem_setOf_eq, hasB_eq, lstM_bit]
  constructor
  · rintro ⟨i, -, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hl x hx, hx, rfl⟩

section Tables

variable {P C V Q : ℕ} (hR : RealT elt P C V Q)
include hR

theorem mulE_elt {x y : ℕ} (hx : x < 128) (hy : y < 128) : elt (mulE P x y) = elt x * elt y :=
  hR.mulP hx hy

omit hR in
theorem powE_lt (x : ℕ) : ∀ k, powE P x k < 128
  | 0 => by
    change 0 < 128
    decide
  | _ + 1 => atR_lt _ _

theorem powE_elt {x : ℕ} (hx : x < 128) : ∀ k, elt (powE P x k) = elt x ^ k
  | 0 => by
    change elt 0 = _
    rw [hR.one, pow_zero]
  | k + 1 => by
    change elt (mulE P (powE P x k) x) = _
    rw [mulE_elt hR (powE_lt x k) hx, powE_elt hx k, pow_succ]

theorem stepK_mset {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) (M : ℕ) :
    mset elt (stepK C gs M) = mset elt M ∪ {y | ∃ g ∈ gs, ∃ x ∈ mset elt M, x * elt g = y} := by
  ext y
  constructor
  · rintro ⟨k, hk, hb, rfl⟩
    rw [hasB_eq, stepK_bit] at hb
    rcases hb with hb | ⟨g, hg, hb⟩
    · exact Or.inl ⟨k, hk, by rw [hasB_eq]; exact hb, rfl⟩
    · have hm : elt k ∈ mset elt (imgR (rowT C g) M) := ⟨k, hk, by rw [hasB_eq]; exact hb, rfl⟩
      rw [mset_imgR_right hR (hgs g hg)] at hm
      obtain ⟨x, hx, he⟩ := hm
      exact Or.inr ⟨g, hg, x, hx, he⟩
  · rintro (⟨k, hk, hb, rfl⟩ | ⟨g, hg, x, hx, rfl⟩)
    · refine ⟨k, hk, ?_, rfl⟩
      rw [hasB_eq, stepK_bit]
      rw [hasB_eq] at hb
      exact Or.inl hb
    · have hm : x * elt g ∈ mset elt (imgR (rowT C g) M) := by
        rw [mset_imgR_right hR (hgs g hg)]
        exact ⟨x, hx, rfl⟩
      obtain ⟨k, hk, hb, he⟩ := hm
      refine ⟨k, hk, ?_, he⟩
      rw [hasB_eq, stepK_bit]
      rw [hasB_eq] at hb
      exact Or.inr ⟨g, hg, hb⟩

omit hR in
theorem closK_succ (gs : List ℕ) (R : ℕ) : closK C gs (R + 1) = stepK C gs (closK C gs R) := by
  change strictN (closK C gs R) (stepK C gs) = _
  rw [strictN_eq]

theorem closK_closure {gs : List ℕ} (hgs : ∀ g ∈ gs, g < 128) {R : ℕ} (hc : closOK C gs R = true) :
    mset elt (closK C gs R) = (Subgroup.closure {x | ∃ g ∈ gs, elt g = x} : Set G) := by
  set S : Set G := {x | ∃ g ∈ gs, elt g = x}
  have hsub : ∀ R, mset elt (closK C gs R) ⊆ (Subgroup.closure S : Set G) := by
    intro R
    induction R with
    | zero =>
      change mset elt 1 ⊆ _
      rw [mset_one hR.one]
      rintro _ rfl
      exact (Subgroup.closure S).one_mem
    | succ R ih =>
      rw [closK_succ, stepK_mset hR hgs]
      rintro y (hy | ⟨g, hg, x, hx, rfl⟩)
      · exact ih hy
      · exact (Subgroup.closure S).mul_mem (ih hx) (Subgroup.subset_closure ⟨g, hg, rfl⟩)
  have hone : ∀ R, (1 : G) ∈ mset elt (closK C gs R) := by
    intro R
    induction R with
    | zero =>
      change (1 : G) ∈ mset elt 1
      rw [mset_one hR.one]
      rfl
    | succ R ih =>
      rw [closK_succ, stepK_mset hR hgs]
      exact Or.inl ih
  set T := mset elt (closK C gs R) with hT
  have hfix : stepK C gs (closK C gs R) = closK C gs R := by
    change strictB (closK C gs R) (fun M => Nat.beq (stepK C gs M) M) = true at hc
    rw [strictB_eq] at hc
    exact Nat.eq_of_beq_eq_true hc
  have hcl : ∀ x ∈ T, ∀ g ∈ gs, x * elt g ∈ T := by
    intro x hx g hg
    have := stepK_mset hR hgs (closK C gs R)
    rw [hfix] at this
    rw [hT, this]
    exact Or.inr ⟨g, hg, x, hx, rfl⟩
  have hfin : T.Finite := by
    refine ((Set.finite_Iio 128).image elt).subset ?_
    rintro _ ⟨i, hi, -, rfl⟩
    exact ⟨i, hi, rfl⟩
  have hinv : ∀ x ∈ T, ∀ g ∈ gs, x * (elt g)⁻¹ ∈ T := by
    intro x hx g hg
    have himg : (fun y => y * elt g) '' T = T := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ hfin
      · rintro _ ⟨y, hy, rfl⟩
        exact hcl y hy g hg
      · rw [Set.InjOn.ncard_image fun a _ b _ h => mul_right_cancel h]
    rw [← himg] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  refine Set.Subset.antisymm (hsub R) fun x hx => ?_
  refine Subgroup.closure_induction_right (p := fun x _ => x ∈ T) (hone R) ?_ ?_ hx
  · rintro x - _ ⟨g, hg, rfl⟩ hxT
    exact hcl x hxT g hg
  · rintro x - _ ⟨g, hg, rfl⟩ hxT
    exact hinv x hxT g hg

theorem cenE_mset (X : ℕ) {y : ℕ} (hy : y < 128) :
    mset elt (cenE P C X y) = {x | x ∈ mset elt X ∧ x * elt y = elt y * x} := by
  have e : cenE P C X y = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(bAnd(hasB X i, Nat.beq (atR (rowT P i) y) (atR (rowT C i) y)),
        Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128 := by
    simp only [cenE, strictN_eq]
  rw [e, mset_recMaskId]
  ext x
  constructor
  · rintro ⟨i, hi, hc, rfl⟩
    rw [bAnd_eq, Bool.and_eq_true] at hc
    refine ⟨⟨i, hi, hc.1, rfl⟩, ?_⟩
    have := congrArg elt (Nat.eq_of_beq_eq_true hc.2)
    rwa [hR.mulP hi hy, hR.mulC hy hi] at this
  · rintro ⟨⟨i, hi, hb, rfl⟩, hc⟩
    refine ⟨i, hi, ?_, rfl⟩
    rw [bAnd_eq, hb, Bool.true_and, Nat.beq_eq]
    refine hR.inj _ (atR_lt _ _) _ (atR_lt _ _) ?_
    rw [hR.mulP hi hy, hR.mulC hy hi]
    exact hc

theorem involM_mset (X : ℕ) :
    mset elt (involM Q X) = {x | x ∈ mset elt X ∧ x ≠ 1 ∧ x * x = 1} := by
  have e : involM Q X = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(bAnd(hasB X i, bAnd(Nat.blt 0 i, Nat.beq (atR Q i) 0)),
        Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128 := by
    simp only [involM, strictN_eq]
  rw [e, mset_recMaskId]
  have hq : ∀ i < 128, atR Q i = 0 ↔ elt i * elt i = 1 := fun i hi => by
    rw [← hR.sq hi, ← hR.one]
    exact ⟨fun h => by rw [h], fun h => hR.inj _ (atR_lt _ _) _ (by decide) h⟩
  have h0 : ∀ i < 128, 0 < i ↔ elt i ≠ 1 := fun i hi => by
    rw [← hR.one]
    exact ⟨fun h he => by have := hR.inj _ hi _ (by decide) he; omega,
      fun h => Nat.pos_of_ne_zero fun h' => h (by rw [h'])⟩
  ext x
  constructor
  · rintro ⟨i, hi, hc, rfl⟩
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    exact ⟨⟨i, hi, hc.1, rfl⟩, (h0 i hi).1 hc.2.1, (hq i hi).1 hc.2.2⟩
  · rintro ⟨⟨i, hi, hb, rfl⟩, h1, h2⟩
    refine ⟨i, hi, ?_, rfl⟩
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
    exact ⟨hb, (h0 i hi).2 h1, (hq i hi).2 h2⟩

theorem clsE_mset (X : ℕ) {y : ℕ} (hy : y < 128) :
    mset elt (clsE P C V X y) = {g | ∃ x ∈ mset elt X, x * elt y * x⁻¹ = g} := by
  have e : clsE P C V X y = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR (rowT P i) (rowT C (atR V i)) y)), acc))
      128 := by
    simp only [clsE, strictN_eq]
  rw [e, mset_recMask (hasB X) (fun i => conjR (rowT P i) (rowT C (atR V i)) y)
    fun _ _ => atR_lt _ _]
  ext g
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    exact ⟨elt i, ⟨i, hi, hb, rfl⟩, (conjR_elt hR hi hy).symm⟩
  · rintro ⟨_, ⟨i, hi, hb, rfl⟩, rfl⟩
    exact ⟨i, hi, hb, conjR_elt hR hi hy⟩

omit hR in
theorem mset_recLorIf (B : ℕ) (F : ℕ → ℕ) :
    mset elt (Nat.rec (motive := fun _ => Nat) 0 (fun b acc => nIf(hasB B b, Nat.lor acc (F b), acc))
      128) = ⋃ b ∈ {b | b < 128 ∧ hasB B b = true}, mset elt (F b) := by
  ext g
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨k, hk, hb, rfl⟩
    rw [hasB_eq, recLorIf_bit] at hb
    obtain ⟨b, hb', h1, h2⟩ := hb
    exact ⟨b, ⟨hb', h1⟩, k, hk, by rw [hasB_eq]; exact h2, rfl⟩
  · rintro ⟨b, ⟨hb', h1⟩, k, hk, h2, rfl⟩
    refine ⟨k, hk, ?_, rfl⟩
    rw [hasB_eq, recLorIf_bit]
    rw [hasB_eq] at h2
    exact ⟨b, hb', h1, h2⟩

theorem prodM_mset (A B : ℕ) :
    mset elt (prodM C A B) = {g | ∃ a ∈ mset elt A, ∃ b ∈ mset elt B, a * b = g} := by
  have e : prodM C A B = Nat.rec (motive := fun _ => Nat) 0 (fun b acc =>
      nIf(hasB B b, Nat.lor acc (imgR (rowT C b) A), acc)) 128 := by
    simp only [prodM, strictN_eq]
  rw [e, mset_recLorIf]
  ext g
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨b, ⟨hb, h1⟩, hg⟩
    rw [mset_imgR_right hR hb] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact ⟨a, ha, elt b, ⟨b, hb, h1, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨b, hb, h1, rfl⟩, rfl⟩
    refine ⟨b, ⟨hb, h1⟩, ?_⟩
    rw [mset_imgR_right hR hb]
    exact ⟨a, ha, rfl⟩

theorem lprodM_mset (B A : ℕ) :
    mset elt (lprodM P B A) = {g | ∃ b ∈ mset elt B, ∃ a ∈ mset elt A, b * a = g} := by
  have e : lprodM P B A = Nat.rec (motive := fun _ => Nat) 0 (fun b acc =>
      nIf(hasB B b, Nat.lor acc (imgR (rowT P b) A), acc)) 128 := by
    simp only [lprodM, strictN_eq]
  rw [e, mset_recLorIf]
  ext g
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨b, ⟨hb, h1⟩, hg⟩
    rw [mset_imgR_left hR hb] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact ⟨elt b, ⟨b, hb, h1, rfl⟩, a, ha, rfl⟩
  · rintro ⟨_, ⟨b, hb, h1, rfl⟩, a, ha, rfl⟩
    refine ⟨b, ⟨hb, h1⟩, ?_⟩
    rw [mset_imgR_left hR hb]
    exact ⟨a, ha, rfl⟩

theorem permB_spec {A B : ℕ} (h : permB P C A B = true) :
    {g | ∃ a ∈ mset elt A, ∃ b ∈ mset elt B, a * b = g} =
      {g | ∃ b ∈ mset elt B, ∃ a ∈ mset elt A, b * a = g} := by
  rw [← prodM_mset hR, ← lprodM_mset hR, Nat.eq_of_beq_eq_true h]

theorem elemAbK_spec {X : ℕ} (h : elemAbK P C Q X = true) :
    ∀ x ∈ mset elt X, x * x = 1 ∧ ∀ w ∈ mset elt X, w * x = x * w := by
  change strictB X (fun X => allBelow 128 2 fun x =>
    bIf(hasB X x, bAnd(Nat.beq (atR Q x) 0, Nat.beq (cenE P C X x) X), true)) = true at h
  rw [strictB_eq] at h
  rintro _ ⟨i, hi, hb, rfl⟩
  have := allBelow_spec h (by decide) i hi
  rw [hb, bAnd_eq, Bool.and_eq_true] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨?_, fun w hw => ?_⟩
  · rw [← hR.sq hi, Nat.eq_of_beq_eq_true h1, hR.one]
  · rw [← Nat.eq_of_beq_eq_true h2, cenE_mset hR X hi] at hw
    exact hw.2

end Tables

end CFSG.KC.G2Three.Sec1T3
