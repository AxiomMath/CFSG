module

public import Certificates.Data.Kernel.G2Three.Sec1T3B
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop
open scoped commutatorElement

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem not'_eq (b : Bool) : Bool.not' b = !b := by cases b <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem recAnd_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n = true ↔
      ∀ i < n, f i = true
  | 0 => by
    change true = true ↔ _
    simp
  | n + 1 => by
    change bAnd(f n, Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, recAnd_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem recOr_of (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) false (fun t ih => bIf(f t, true, ih)) n = true →
      ∃ t < n, f t = true
  | 0, h => (Bool.false_ne_true h).elim
  | n + 1, h => by
    change Bool.rec (motive := fun _ => Bool)
      (Nat.rec (motive := fun _ => Bool) false (fun t ih => bIf(f t, true, ih)) n) true (f n) =
        true at h
    cases hf : f n
    · rw [hf] at h
      obtain ⟨t, ht, h2⟩ := recOr_of f n h
      exact ⟨t, Nat.lt_succ_of_lt ht, h2⟩
    · exact ⟨n, Nat.lt_succ_self n, hf⟩

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi)
    (i : ℕ) (him : i < m) : f i = true := by
  have h1 := (recAnd_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi).1
    h (i / 64) (by omega)
  have h2 := (recAnd_iff (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, (rfl : (2 : ℕ) ^ 6 = 64)]
    omega
  have hb : Nat.blt i m = true := by rw [Nat.blt_eq]; exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem hasB_eq (m i : ℕ) : hasB m i = m.testBit i := by
  have key : m &&& 1 <<< i = 0 ↔ m.testBit i = false := by
    rw [Nat.one_shiftLeft]
    constructor
    · intro h
      have := congrArg (fun n => n.testBit i) h
      simpa [Nat.testBit_and, Nat.testBit_two_pow] using this
    · intro h
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : i = j
      · subst hj
        simp [h]
      · simp [hj]
  unfold hasB
  change Nat.blt 0 (m &&& 1 <<< i) = _
  cases hb : m.testBit i
  · rw [key.2 hb]
    rfl
  · have : m &&& 1 <<< i ≠ 0 := fun h => by
      rw [key.1 h] at hb
      exact absurd hb (by decide)
    rw [Nat.blt_eq]
    exact Nat.pos_of_ne_zero this

theorem fld127_lt (r o : ℕ) : fld(r, o, 127) < 128 :=
  Nat.lt_succ_of_le Nat.and_le_right

theorem atR_lt (r j : ℕ) : atR r j < 128 := fld127_lt _ _

theorem recMask_bit (c : ℕ → Bool) (g : ℕ → ℕ) (k : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.lor acc (Nat.shiftLeft 1 (g i)), acc)) n).testBit k = true ↔
      ∃ i < n, c i = true ∧ g i = k
  | 0 => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | n + 1 => by
    have ih := recMask_bit c g k n
    change (nIf(c n, Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.lor acc (Nat.shiftLeft 1 (g i)), acc)) n) (Nat.shiftLeft 1 (g n)),
      Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.lor acc (Nat.shiftLeft 1 (g i)), acc)) n)).testBit k = true ↔ _
    generalize Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(c i, Nat.lor acc (Nat.shiftLeft 1 (g i)), acc)) n = R at ih ⊢
    cases hc : c n
    · change R.testBit k = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨i, hi, h1, h2⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h1, h2⟩
        · rw [hc] at h1
          exact absurd h1 (by decide)
    · change (R ||| 1 <<< g n).testBit k = true ↔ _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih,
        decide_eq_true_eq]
      constructor
      · rintro (⟨i, hi, h1, h2⟩ | h)
        · exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩
        · exact ⟨n, Nat.lt_succ_self n, hc, h⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl ⟨i, hi, h1, h2⟩
        · exact Or.inr h2

theorem recLor_bit (g : ℕ → ℕ) (k : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Nat) 0 (fun t acc => Nat.lor acc (g t)) n).testBit k = true ↔
      ∃ t < n, (g t).testBit k = true
  | 0 => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | n + 1 => by
    change (Nat.rec (motive := fun _ => Nat) 0 (fun t acc => Nat.lor acc (g t)) n |||
      g n).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, recLor_bit g k n]
    constructor
    · rintro (⟨t, ht, h⟩ | h)
      · exact ⟨t, Nat.lt_succ_of_lt ht, h⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inl ⟨t, ht, h⟩
      · exact Or.inr h

theorem testBit_two_pow_sub_two (N k : ℕ) : (2 ^ N - 2).testBit k = true ↔ 0 < k ∧ k < N := by
  have hdiv : (2 ^ N - 2) / 2 = 2 ^ (N - 1) - 1 := by
    rcases N with _ | n
    · rfl
    · have : 2 ^ (n + 1) - 2 = 2 * (2 ^ n - 1) := by rw [pow_succ]; omega
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
      rfl
  have hmod : (2 ^ N - 2) % 2 = 0 := by
    rcases N with _ | n
    · rfl
    · have : 2 ^ (n + 1) - 2 = 2 * (2 ^ n - 1) := by rw [pow_succ]; omega
      rw [this, Nat.mul_mod_right]
  rcases k with _ | j
  · rw [Nat.testBit_zero, hmod]
    simp
  · rw [Nat.testBit_succ, hdiv, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    omega

variable {G : Type} [Group G] (elt : ℕ → G)

@[expose] def RepM (m : ℕ) (X : Set G) : Prop :=
  (∀ i < 128, hasB m i = true ↔ elt i ∈ X) ∧ ∀ x ∈ X, ∃ i < 128, elt i = x

@[expose] def RealT (P C V Q : ℕ) : Prop :=
  elt 0 = 1 ∧
  (∀ i < 128, ∀ j < 128, atR (rowT P i) j < 128 ∧ elt (atR (rowT P i) j) = elt i * elt j) ∧
  (∀ i < 128, ∀ j < 128, atR (rowT C j) i = atR (rowT P i) j) ∧
  (∀ i < 128, atR V i < 128 ∧ elt (atR V i) = (elt i)⁻¹) ∧
  (∀ i < 128, atR Q i = atR (rowT P i) i) ∧
  ∀ i < 128, ∀ j < 128, elt i = elt j → i = j

@[expose] def mset (m : ℕ) : Set G := {g | ∃ i < 128, hasB m i = true ∧ elt i = g}

variable {elt}

theorem RepM.eq_mset {m : ℕ} {X : Set G} (h : RepM elt m X) : X = mset elt m := by
  ext g
  constructor
  · intro hg
    obtain ⟨i, hi, rfl⟩ := h.2 g hg
    exact ⟨i, hi, (h.1 i hi).2 hg, rfl⟩
  · rintro ⟨i, hi, hb, rfl⟩
    exact (h.1 i hi).1 hb

theorem repM_mset (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) (m : ℕ) :
    RepM elt m (mset elt m) := by
  refine ⟨fun i hi => ⟨fun hb => ⟨i, hi, hb, rfl⟩, ?_⟩, fun x ⟨i, hi, _, he⟩ => ⟨i, hi, he⟩⟩
  rintro ⟨j, hj, hb, he⟩
  rwa [← hinj j hj i hi he]

theorem mem_mset_iff (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) {m i : ℕ}
    (hi : i < 128) : elt i ∈ mset elt m ↔ hasB m i = true :=
  ((repM_mset hinj m).1 i hi).symm

theorem mset_lor (a b : ℕ) : mset elt (Nat.lor a b) = mset elt a ∪ mset elt b := by
  ext g
  simp only [mset, Set.mem_setOf_eq, Set.mem_union, hasB_eq]
  change (∃ i < 128, (a ||| b).testBit i = true ∧ elt i = g) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  constructor
  · rintro ⟨i, hi, h | h, he⟩
    · exact Or.inl ⟨i, hi, h, he⟩
    · exact Or.inr ⟨i, hi, h, he⟩
  · rintro (⟨i, hi, h, he⟩ | ⟨i, hi, h, he⟩)
    · exact ⟨i, hi, Or.inl h, he⟩
    · exact ⟨i, hi, Or.inr h, he⟩

theorem imgR_bit (r H k : ℕ) :
    hasB (imgR r H) k = true ↔ ∃ i < 128, hasB H i = true ∧ atR r i = k := by
  rw [hasB_eq]
  exact recMask_bit (hasB H) (atR r) k 128

theorem mset_imgR (r H : ℕ) (f : G → G) (hr : ∀ i < 128, elt (atR r i) = f (elt i)) :
    mset elt (imgR r H) = f '' mset elt H := by
  ext g
  constructor
  · rintro ⟨k, -, hk, rfl⟩
    obtain ⟨i, hi, hb, rfl⟩ := (imgR_bit r H k).1 hk
    exact ⟨elt i, ⟨i, hi, hb, rfl⟩, (hr i hi).symm⟩
  · rintro ⟨_, ⟨i, hi, hb, rfl⟩, rfl⟩
    exact ⟨atR r i, atR_lt r i, (imgR_bit r H _).2 ⟨i, hi, hb, rfl⟩, hr i hi⟩

section Tables

variable {P C V Q : ℕ} (hR : RealT elt P C V Q)
include hR

theorem RealT.one : elt 0 = 1 := hR.1

theorem RealT.mulP {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    elt (atR (rowT P i) j) = elt i * elt j := (hR.2.1 i hi j hj).2

theorem RealT.mulC {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    elt (atR (rowT C j) i) = elt i * elt j := by
  rw [hR.2.2.1 i hi j hj]
  exact hR.mulP hi hj

theorem RealT.inv {i : ℕ} (hi : i < 128) : elt (atR V i) = (elt i)⁻¹ := (hR.2.2.2.1 i hi).2

theorem RealT.sq {i : ℕ} (hi : i < 128) : elt (atR Q i) = elt i * elt i := by
  rw [hR.2.2.2.2.1 i hi]
  exact hR.mulP hi hi

theorem RealT.inj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j := hR.2.2.2.2.2

theorem conjR_elt {x g : ℕ} (hx : x < 128) (hg : g < 128) :
    elt (conjR (rowT P x) (rowT C (atR V x)) g) = elt x * elt g * (elt x)⁻¹ := by
  unfold conjR
  rw [hR.mulC (atR_lt _ _) (atR_lt _ _), hR.mulP hx hg, hR.inv hx]

theorem commE_elt {x y : ℕ} (hx : x < 128) (hy : y < 128) :
    elt (commE P C V x y) = ⁅elt x, elt y⁆ := by
  unfold commE
  rw [hR.mulC (i := conjR (rowT P x) (rowT C (atR V x)) y) (atR_lt _ _) (atR_lt _ _),
    conjR_elt hR hx hy, hR.inv hy, commutatorElement_def]

theorem mset_imgR_left {x : ℕ} (hx : x < 128) (H : ℕ) :
    mset elt (imgR (rowT P x) H) = (elt x * ·) '' mset elt H :=
  mset_imgR _ H _ fun _ hi => hR.mulP hx hi

theorem mset_imgR_right {x : ℕ} (hx : x < 128) (H : ℕ) :
    mset elt (imgR (rowT C x) H) = (· * elt x) '' mset elt H :=
  mset_imgR _ H _ fun _ hi => hR.mulC hi hx

end Tables

theorem pop_eq (m : ℕ) : ∀ n,
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc => nIf(hasB m i, Nat.succ acc, acc)) n =
      ((Finset.range n).filter fun i => hasB m i = true).card
  | 0 => rfl
  | n + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert]
    change nIf(hasB m n, Nat.succ (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(hasB m i, Nat.succ acc, acc)) n), Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => nIf(hasB m i, Nat.succ acc, acc)) n) = _
    rw [pop_eq m n]
    cases hb : hasB m n
    · rfl
    · simp only [if_true]
      rw [Finset.card_insert_of_notMem (by simp)]

theorem pop_sound (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j) {m : ℕ} {X : Set G}
    (h : RepM elt m X) : X.ncard = pop m := by
  have e : X = elt '' ↑((Finset.range 128).filter fun i => hasB m i = true) := by
    rw [h.eq_mset]
    ext g
    simp [mset, and_assoc]
  rw [e, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  · exact (pop_eq m 128).symm
  · intro i hi j hj he
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
    exact hinj i hi.1 j hj.1 he

section Lattice

theorem ext_subgroup (H : Subgroup G) {x : G} {K : Set G} (hx : x ∉ H)
    (hK1 : K = (H : Set G) ∪ (fun y => y * x) '' (H : Set G))
    (hK2 : K = (H : Set G) ∪ (fun y => x * y) '' (H : Set G))
    (hxx : x * x ∈ H) : ∃ K' : Subgroup G, (K' : Set G) = K := by
  have memK : ∀ g, g ∈ K ↔ g ∈ H ∨ g * x⁻¹ ∈ H := by
    intro g
    rw [hK1]
    constructor
    · rintro (h | ⟨a, ha, rfl⟩)
      · exact Or.inl h
      · right
        simpa using ha
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨g * x⁻¹, h, by simp⟩
  have conj : ∀ b ∈ H, x * b * x⁻¹ ∈ H := by
    intro b hb
    have : x * b ∈ K := by
      rw [hK2]
      exact Or.inr ⟨b, hb, rfl⟩
    rcases (memK _).1 this with h | h
    · exact absurd (by simpa using H.mul_mem h (H.inv_mem hb)) hx
    · exact h
  refine ⟨{ carrier := K, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    rw [memK] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (H.mul_mem ha hb)
    · right
      simpa [mul_assoc] using H.mul_mem ha hb
    · right
      simpa [mul_assoc] using H.mul_mem ha (conj b hb)
    · left
      have := H.mul_mem (H.mul_mem ha (conj _ hb)) hxx
      have e : a * x⁻¹ * (x * (b * x⁻¹) * x⁻¹) * (x * x) = a * b := by group
      rwa [e] at this
  · rw [memK]
    exact Or.inl H.one_mem
  · intro a ha
    rw [memK] at ha ⊢
    rcases ha with ha | ha
    · exact Or.inl (H.inv_mem ha)
    · right
      have := H.mul_mem (H.mul_mem (H.inv_mem hxx)
        (conj _ (H.mul_mem (H.inv_mem ha) (H.inv_mem hxx)))) hxx
      have e : (x * x)⁻¹ * (x * ((a * x⁻¹)⁻¹ * (x * x)⁻¹) * x⁻¹) * (x * x) = a⁻¹ * x⁻¹ := by
        group
      rwa [e] at this

theorem mem_of_mul_closed {s : Set G} (hs : s.Finite) {x : G} (hxx : x * x ∈ s)
    (hcl : ∀ y ∈ s, y * x ∈ s) : x ∈ s := by
  have hpow : ∀ n : ℕ, x ^ (n + 2) ∈ s := by
    intro n
    induction n with
    | zero => simpa [pow_two] using hxx
    | succ n ih =>
      have := hcl _ ih
      rwa [← pow_succ] at this
  obtain ⟨i, j, hij, he⟩ := hs.exists_lt_map_eq_of_forall_mem (f := fun n => x ^ (n + 2)) hpow
  have h1 : x ^ (j - i) = 1 := by
    have e : x ^ (j + 2) = x ^ (i + 2) * x ^ (j - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← he] at e
    exact (mul_left_cancel (a := x ^ (i + 2)) (by rw [mul_one]; exact e)).symm
  have e : x ^ ((j - i - 1) + 2) = x := by
    have e2 : j - i - 1 + 2 = (j - i) + 1 := by omega
    rw [e2, pow_succ, h1, one_mul]
  exact e ▸ hpow _

theorem exists_index_two {K : Subgroup G} [Finite K] (hp : IsPGroup 2 K) (hK : K ≠ ⊥) :
    ∃ M : Subgroup G, M ≤ K ∧ ∃ y ∈ K, y ∉ M ∧ (∀ g ∈ K, g ∉ M → g * y⁻¹ ∈ M) ∧
      y * y ∈ M ∧ (∀ g ∈ M, y * g * y⁻¹ ∈ M) ∧ (K : Set G).ncard = 2 * (M : Set G).ncard := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hp)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hK (Subgroup.card_eq_one.1 (by simpa using hn))
  obtain ⟨M', hM'⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 2
    (n := n - 1) (by rw [hn]; exact pow_dvd_pow 2 (Nat.sub_le n 1))
  have hidx : M'.index = 2 := by
    have h := M'.card_mul_index
    rw [hM', hn] at h
    have e : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [e] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hne : M' ≠ ⊤ := by
    rintro rfl
    rw [Subgroup.index_top] at hidx
    exact absurd hidx (by decide)
  obtain ⟨y', hy'⟩ : ∃ y' : K, y' ∉ M' := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun z _ => h z)
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  have memM : ∀ g : K, (g : G) ∈ M'.map K.subtype ↔ g ∈ M' := by
    intro g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, he⟩
      rwa [← Subtype.ext he]
    · intro hg
      exact ⟨g, hg, rfl⟩
  refine ⟨M'.map K.subtype, Subgroup.map_subtype_le M', y', y'.2, (memM y').not.2 hy', ?_, ?_, ?_,
    ?_⟩
  · intro g hg hgM
    have hg' : (⟨g, hg⟩ : K) ∉ M' := fun h => hgM ((memM ⟨g, hg⟩).2 h)
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g, hg⟩) (b := y'⁻¹)).2
      (iff_of_false hg' (fun h => hy' (by simpa using M'.inv_mem h)))
    exact (memM (⟨g, hg⟩ * y'⁻¹)).2 this
  · exact (memM (y' * y')).2 (Subgroup.mul_self_mem_of_index_two hidx y')
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
    exact (memM (y' * g' * y'⁻¹)).2 (hnorm.conj_mem g' hg' y')
  · have h1 : (K : Set G).ncard = Nat.card K := rfl
    have h2 : ((M'.map K.subtype : Subgroup G) : Set G).ncard = Nat.card M' :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rw [h1, h2, ← M'.card_mul_index, hidx, mul_comm]

theorem lat_math (S : ℕ → Set G) (N : ℕ) (G₀ : Subgroup G) (hfin : (G₀ : Set G).Finite)
    (h2 : IsPGroup 2 G₀) (pr : ℕ → ℕ → G → Prop) (pn : ℕ → ℕ → Prop) (gn : ℕ → Set G)
    (hN : 0 < N) (hS0 : S 0 = {1}) (hle : ∀ h < N, S h ⊆ G₀)
    (hpk : ∀ h < N, ∀ k x, pr h k x → 0 < k ∧ k < N)
    (hp : ∀ h < N, ∀ k x, pr h k x → x ∉ S h ∧ x * x ∈ S h ∧
      S k = S h ∪ (fun y => y * x) '' S h ∧ S k = S h ∪ (fun y => x * y) '' S h)
    (hpn : ∀ h < N, ∀ k, pn h k → k < N ∧ S h ⊆ S k ∧ (S k).ncard = 2 * (S h).ncard)
    (hall : ∀ k, 0 < k → k < N → ∃ h < N, ∃ x, pr h k x)
    (hgn : ∀ h < N, gn h ⊆ S h)
    (hcov : ∀ h < N, ∀ y ∈ G₀, y ∉ S h → (∀ k x, pr h k x → y ∉ S k) →
      (∀ k, pn h k → y ∉ S k) → y * y ∈ S h → ∃ g ∈ gn h, y * g * y⁻¹ ∉ S h) :
    (∀ k < N, ∃ K : Subgroup G, K ≤ G₀ ∧ (K : Set G) = S k) ∧
      ∀ K ≤ G₀, ∃ k < N, (K : Set G) = S k := by
  have hfinS : ∀ k < N, (S k).Finite := fun k hk => hfin.subset (hle k hk)
  have sub : ∀ n, ∀ k < N, (S k).ncard = n → ∃ K : Subgroup G, (K : Set G) = S k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk hn
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨⊥, by rw [hS0]; rfl⟩
      obtain ⟨h, hh, x, hpr⟩ := hall k hk0 hk
      obtain ⟨hx, hxx, hK1, hK2⟩ := hp h hh k x hpr
      have hsub : S h ⊆ S k := by
        rw [hK1]
        exact Set.subset_union_left
      have hss : S h ⊂ S k := by
        refine (Set.ssubset_iff_subset_ne).2 ⟨hsub, fun he => hx ?_⟩
        refine mem_of_mul_closed (hfinS h hh) hxx fun y hy => ?_
        rw [he, hK1]
        exact Or.inr ⟨y, hy, rfl⟩
      obtain ⟨H, hH⟩ := ih _ (hn ▸ Set.ncard_lt_ncard hss (hfinS k hk)) h hh rfl
      rw [← hH] at hx hxx hK1 hK2
      exact ext_subgroup H hx hK1 hK2 hxx
  have sub' : ∀ k < N, ∃ K : Subgroup G, (K : Set G) = S k := fun k hk => sub _ k hk rfl
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := sub' k hk
    exact ⟨K, fun g hg => hle k hk (hK ▸ hg), hK⟩
  suffices ∀ n, ∀ K : Subgroup G, K ≤ G₀ → (K : Set G).ncard = n → ∃ k < N, (K : Set G) = S k from
    fun K hK => this _ K hK rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hK hn
  by_cases hbot : K = ⊥
  · exact ⟨0, hN, by rw [hbot, hS0]; rfl⟩
  have hKfin : (K : Set G).Finite := hfin.subset hK
  have : Finite K := hKfin.to_subtype
  obtain ⟨M, hMK, y, hyK, hyM, hcos, hyy, hconj, hKM⟩ := exists_index_two (h2.to_le hK) hbot
  have hMK' : (M : Set G) ⊂ K := (Set.ssubset_iff_subset_ne).2
    ⟨hMK, fun he => hyM (by rw [← SetLike.mem_coe, he]; exact hyK)⟩
  obtain ⟨h, hh, hMh⟩ := ih _ (hn ▸ Set.ncard_lt_ncard hMK' hKfin) M (hMK.trans hK) rfl
  have hcov' := hcov h hh y (hK hyK) (by rw [← hMh]; exact hyM)
  have hKsub : ∀ k < N, (M : Set G) ⊆ S k → y ∈ S k → (K : Set G) ⊆ S k := by
    intro k hkN hMk hyk g hg
    obtain ⟨Kk, hKk⟩ := sub' k hkN
    rw [← hKk] at hMk hyk ⊢
    by_cases hgM : g ∈ M
    · exact hMk hgM
    · have := Kk.mul_mem (hMk (hcos g hg hgM)) hyk
      simpa using this
  by_cases hD : ∃ k x, pr h k x ∧ y ∈ S k
  swap
  · by_cases hNd : ∃ k, pn h k ∧ y ∈ S k
    · obtain ⟨k, hpr, hyk⟩ := hNd
      obtain ⟨hkN, hsub, hcard⟩ := hpn h hh k hpr
      rw [← hMh] at hsub hcard
      refine ⟨k, hkN, Set.eq_of_subset_of_ncard_le (hKsub k hkN hsub hyk) ?_ (hfinS k hkN)⟩
      rw [hcard, hKM]
    · push Not at hD hNd
      obtain ⟨g, hg, hgo⟩ := hcov' hD hNd (by rw [← hMh]; exact hyy)
      have hgM : g ∈ M := by
        rw [← SetLike.mem_coe, hMh]
        exact hgn h hh hg
      exact absurd (by rw [← hMh]; exact hconj g hgM) hgo
  obtain ⟨k, x, hpr, hyk⟩ := hD
  obtain ⟨-, hkN⟩ := hpk h hh k x hpr
  obtain ⟨-, -, hK1, -⟩ := hp h hh k x hpr
  obtain ⟨Kk, hKk⟩ := sub' k hkN
  rw [← hMh] at hK1
  have hyx : y * x⁻¹ ∈ M := by
    rw [hK1] at hyk
    rcases hyk with h1 | ⟨a, ha, rfl⟩
    · exact absurd h1 hyM
    · simpa using ha
  have hxK : x ∈ K := by
    have := K.mul_mem (K.inv_mem (hMK hyx)) hyK
    simpa using this
  refine ⟨k, hkN, Set.Subset.antisymm (fun g hg => ?_) ?_⟩
  · rw [← hKk]
    have hMKk : ∀ m ∈ M, m ∈ Kk := by
      intro m hm
      rw [← SetLike.mem_coe, hKk, hK1]
      exact Or.inl hm
    have hyKk : y ∈ Kk := by
      rw [← SetLike.mem_coe, hKk]
      exact hyk
    by_cases hgM : g ∈ M
    · exact hMKk g hgM
    · have := Kk.mul_mem (hMKk _ (hcos g hg hgM)) hyKk
      simpa using this
  · rw [hK1]
    rintro g (hg | ⟨a, ha, rfl⟩)
    · exact hMK hg
    · exact K.mul_mem (hMK ha) hxK

end Lattice

noncomputable abbrev pairK (lo t : ℕ) : ℕ := Nat.land (pairAt lo t) 511

noncomputable abbrev pairX (lo t : ℕ) : ℕ := Nat.shiftRight (pairAt lo t) 9

noncomputable abbrev latM (L k : ℕ) : ℕ := fld(L, Nat.mul 128 k, M128)

theorem getD_eq_getElem' {l : List ℕ} {j : ℕ} (h : j < l.length) : l.getD j 0 = l[j] := by
  simp [List.getD_eq_getElem?_getD, h]

abbrev latG (LG h : ℕ) : ℕ := fld(LG, Nat.mul 64 h, Nat.sub (Nat.shiftLeft 1 64) 1)

abbrev genL (gs t : ℕ) : ℕ := fld(gs, Nat.add 3 (Nat.mul 7 t), 127)

theorem pairX_lt (lo t : ℕ) : pairX lo t < 128 := by
  have h : pairAt lo t ≤ 65535 := Nat.and_le_right
  change pairAt lo t >>> 9 < 128
  rw [Nat.shiftRight_eq_div_pow]
  omega

noncomputable abbrev desD (lo : ℕ) : ℕ := fld(lo, 8, 255)

theorem pairsOK_spec {P C Q L OR h H lo : ℕ} (hp : pairsOK P C Q L OR h H lo = true) :
    ∀ t < Nat.land lo 255,
      (t < desD lo → hasB H (pairX lo t) = false ∧ hasB H (atR Q (pairX lo t)) = true ∧
        latM L (pairK lo t) = Nat.lor H (imgR (rowT C (pairX lo t)) H) ∧
        latM L (pairK lo t) = Nat.lor H (imgR (rowT P (pairX lo t)) H)) ∧
      (desD lo ≤ t → Nat.land H (latM L (pairK lo t)) = H ∧
        ordAt OR (pairK lo t) = 2 * ordAt OR h) := by
  intro t ht
  have hf := (recAnd_iff (fun t => bIf(Nat.blt t (desD lo),
    bAnd(Bool.not' (hasB H (pairX lo t)), bAnd(hasB H (atR Q (pairX lo t)), bAnd(
      Nat.beq (latM L (pairK lo t)) (Nat.lor H (imgR (rowT C (pairX lo t)) H)),
      Nat.beq (latM L (pairK lo t)) (Nat.lor H (imgR (rowT P (pairX lo t)) H))))),
    bAnd(Nat.beq (Nat.land H (latM L (pairK lo t))) H,
      Nat.beq (ordAt OR (pairK lo t)) (Nat.mul 2 (ordAt OR h))))) _).1 hp t ht
  refine ⟨fun hlt => ?_, fun hle => ?_⟩
  · have hb : Nat.blt t (desD lo) = true := by rw [Nat.blt_eq]; exact hlt
    rw [hb] at hf
    simp only [bAnd_eq, Bool.and_eq_true, not'_eq, Bool.not_eq_true', Nat.beq_eq] at hf
    exact hf
  · have hb : Nat.blt t (desD lo) = false := by
      cases hb : Nat.blt t (desD lo)
      · rfl
      · rw [Nat.blt_eq] at hb
        omega
    rw [hb] at hf
    simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hf
    exact hf

theorem gensIn_spec {H gs : ℕ} (h : gensIn H gs = true) :
    ∀ t < Nat.land gs 7, hasB H (genL gs t) = true :=
  (recAnd_iff (fun t => hasB H (genL gs t)) _).1 h

theorem witB_spec {rx cv H gs : ℕ} (h : witB rx cv H gs = true) :
    ∃ t < Nat.land gs 7, hasB H (conjR rx cv (genL gs t)) = false := by
  obtain ⟨t, ht, h⟩ := recOr_of (fun t => Bool.not' (hasB H (conjR rx cv (genL gs t)))) _ h
  rw [not'_eq, Bool.not_eq_true'] at h
  exact ⟨t, ht, h⟩

theorem unionU_bit (L lo x : ℕ) :
    hasB (unionU L lo) x = true ↔ ∃ t < Nat.land lo 255, hasB (latM L (pairK lo t)) x = true := by
  simp only [hasB_eq]
  exact recLor_bit (fun t => latM L (pairK lo t)) x _

theorem idxU_bit (lo k : ℕ) :
    (idxU lo).testBit k = true ↔ ∃ t < desD lo, pairK lo t = k := by
  refine (recLor_bit (fun t => Nat.shiftLeft 1 (pairK lo t)) k _).trans
    (exists_congr fun t => and_congr_right fun _ => ?_)
  change (1 <<< pairK lo t).testBit k = true ↔ _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]

theorem idxAll_bit (k : ℕ) : ∀ LO : List ℕ,
    (idxAll LO).testBit k = true ↔ ∃ lo ∈ LO, (idxU lo).testBit k = true
  | [] => by
    change (0 : ℕ).testBit k = true ↔ _
    simp
  | lo :: LO => by
    change (idxU lo ||| idxAll LO).testBit k = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, idxAll_bit k LO]
    simp

theorem rowsOK_cons (P C V Q G' L LG OR lo : ℕ) (LO : List ℕ) (h : ℕ) :
    rowsOK P C V Q G' L LG OR (lo :: LO) h =
      (rowOK P C V Q G' L LG OR h lo && rowsOK P C V Q G' L LG OR LO (h + 1)) := by
  change bAnd(rowOK P C V Q G' L LG OR h lo,
    strictB (Nat.succ h) (fun h => rowsOK P C V Q G' L LG OR LO h)) = _
  rw [bAnd_eq, strictB_eq]

theorem rowsOK_append (P C V Q G' L LG OR : ℕ) : ∀ (A B : List ℕ) (h : ℕ),
    rowsOK P C V Q G' L LG OR (A ++ B) h =
      (rowsOK P C V Q G' L LG OR A h && rowsOK P C V Q G' L LG OR B (h + A.length))
  | [], B, h => by
    change _ = (true && _)
    simp
  | lo :: A, B, h => by
    rw [List.cons_append, rowsOK_cons, rowsOK_cons, rowsOK_append P C V Q G' L LG OR A B (h + 1),
      List.length_cons, Bool.and_assoc]
    congr 3
    omega

theorem idxAll_append : ∀ A B : List ℕ, idxAll (A ++ B) = Nat.lor (idxAll A) (idxAll B)
  | [], B => by
    change idxAll B = 0 ||| idxAll B
    rw [Nat.zero_or]
  | lo :: A, B => by
    change idxU lo ||| idxAll (A ++ B) = (idxU lo ||| idxAll A) ||| idxAll B
    rw [idxAll_append A B]
    change idxU lo ||| (idxAll A ||| idxAll B) = _
    rw [Nat.or_assoc]

theorem rowsLtK_cons (N lo : ℕ) (LO : List ℕ) :
    rowsLtK N (lo :: LO) = (rowLtK N lo && rowsLtK N LO) := bAnd_eq _ _

theorem rowsLtK_append (N : ℕ) : ∀ A B : List ℕ,
    rowsLtK N (A ++ B) = (rowsLtK N A && rowsLtK N B)
  | [], B => by
    change _ = (true && _)
    simp
  | lo :: A, B => by
    rw [List.cons_append, rowsLtK_cons, rowsLtK_cons, rowsLtK_append N A B, Bool.and_assoc]

theorem rowsLtK_spec {N : ℕ} : ∀ {LO : List ℕ}, rowsLtK N LO = true → ∀ lo ∈ LO,
    desD lo ≤ Nat.land lo 255 ∧ ∀ t < Nat.land lo 255, pairK lo t < N
  | [], _, lo, hlo => absurd hlo (by simp)
  | l :: LO, h, lo, hlo => by
    rw [rowsLtK_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hlo with rfl | hlo
    · have h1 := h.1
      change bAnd(Nat.ble (desD lo) (Nat.land lo 255), Nat.rec (motive := fun _ => Bool) true
        (fun t ih => bAnd(Nat.blt (pairK lo t) N, ih)) (Nat.land lo 255)) = true at h1
      rw [bAnd_eq, Bool.and_eq_true, recAnd_iff] at h1
      exact ⟨Nat.le_of_ble_eq_true h1.1, fun t ht => by
        have := h1.2 t ht
        rwa [Nat.blt_eq] at this⟩
    · exact rowsLtK_spec h.2 lo hlo

theorem ordK_spec {L OR m : ℕ} (h : ordK L OR 0 m = true) (hm : m ≤ 448) :
    ∀ k < m, pop (latM L k) = ordAt OR k := by
  intro k hk
  have := allBelow_spec h (by omega) k hk
  have e : Nat.add 0 k = k := Nat.zero_add k
  rw [e] at this
  exact Nat.eq_of_beq_eq_true this

theorem rowsOK_spec {P C V Q G' L LG OR : ℕ} : ∀ (LO : List ℕ) (h : ℕ),
    rowsOK P C V Q G' L LG OR LO h = true →
      ∀ j < LO.length, rowOK P C V Q G' L LG OR (h + j) (LO.getD j 0) = true
  | [], _, _, j, hj => absurd hj (by simp)
  | lo :: LO, h, hr, j, hj => by
    change bAnd(rowOK P C V Q G' L LG OR h lo,
      strictB (Nat.succ h) (fun h => rowsOK P C V Q G' L LG OR LO h)) = true at hr
    rw [bAnd_eq, Bool.and_eq_true, strictB_eq] at hr
    rcases j with _ | j
    · simpa using hr.1
    · have := rowsOK_spec LO (h + 1) hr.2 j (by simpa using hj)
      have e : h + 1 + j = h + (j + 1) := by omega
      rwa [e] at this

theorem rowOK_spec {P C V Q G' L LG OR h lo : ℕ} (hr : rowOK P C V Q G' L LG OR h lo = true) :
    Nat.land (latM L h) G' = latM L h ∧ gensIn (latM L h) (latG LG h) = true ∧
      pairsOK P C Q L OR h (latM L h) lo = true ∧
      coverOK P C V Q G' (latM L h) (unionU L lo) (latG LG h) = true := by
  simpa only [rowOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] using hr

theorem subset_of_land {H K : ℕ} (h : Nat.land H K = H) : mset elt H ⊆ mset elt K := by
  rintro _ ⟨i, hi, hb, rfl⟩
  refine ⟨i, hi, ?_, rfl⟩
  rw [← h, hasB_eq] at hb
  change (H &&& K).testBit i = true at hb
  rw [Nat.testBit_and, Bool.and_eq_true] at hb
  rw [hasB_eq]
  exact hb.2

theorem lat_sound {P C V Q GM L LG OR N : ℕ} {LO : List ℕ} {G₀ : Subgroup G}
    (hR : RealT elt P C V Q) (hG : RepM elt GM (G₀ : Set G)) (h2 : IsPGroup 2 G₀)
    (hr : rowsOK P C V Q GM L LG OR LO 0 = true) (hi : idxAll LO = 2 ^ N - 2)
    (h0 : fld(L, 0, M128) = 1) (hn : LO.length = N) (ho : ordK L OR 0 N = true)
    (hlt : rowsLtK N LO = true) (hN : 0 < N) (hN' : N ≤ 448) :
    (∀ k < N, ∃ K : Subgroup G, K ≤ G₀ ∧ RepM elt (latM L k) (K : Set G)) ∧
      ∀ K ≤ G₀, ∃ k < N, RepM elt (latM L k) (K : Set G) := by
  have hinj := hR.inj
  set S : ℕ → Set G := fun k => mset elt (latM L k) with hSdef
  have hrow : ∀ h < N, rowOK P C V Q GM L LG OR h (LO.getD h 0) = true := fun h hh => by
    simpa using rowsOK_spec LO 0 hr h (hn ▸ hh)
  have hmemLO : ∀ h < N, LO.getD h 0 ∈ LO := fun h hh => by
    rw [getD_eq_getElem' (hn ▸ hh)]
    exact List.getElem_mem _
  have hrowLt : ∀ h < N, desD (LO.getD h 0) ≤ Nat.land (LO.getD h 0) 255 ∧
      ∀ t < Nat.land (LO.getD h 0) 255, pairK (LO.getD h 0) t < N :=
    fun h hh => rowsLtK_spec hlt _ (hmemLO h hh)
  have hmem : ∀ {m i : ℕ}, i < 128 → (elt i ∈ mset elt m ↔ hasB m i = true) :=
    fun hi => mem_mset_iff hinj hi
  have hcard : ∀ k < N, (S k).ncard = ordAt OR k := fun k hk => by
    rw [pop_sound hinj (repM_mset hinj _)]
    exact ordK_spec ho hN' k hk
  let pr : ℕ → ℕ → G → Prop := fun h k x =>
    ∃ t < desD (LO.getD h 0), pairK (LO.getD h 0) t = k ∧ elt (pairX (LO.getD h 0) t) = x
  let pn : ℕ → ℕ → Prop := fun h k =>
    ∃ t < Nat.land (LO.getD h 0) 255, desD (LO.getD h 0) ≤ t ∧ pairK (LO.getD h 0) t = k
  let gn : ℕ → Set G := fun h => {g | ∃ t < Nat.land (latG LG h) 7, elt (genL (latG LG h) t) = g}
  have hfin : (G₀ : Set G).Finite := by
    refine ((Set.finite_Iio 128).image elt).subset fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := hG.2 x hx
    exact ⟨i, hi, rfl⟩
  have hS0 : S 0 = {1} := by
    have e : latM L 0 = 1 := h0
    simp only [hSdef, e]
    ext g
    simp only [mset, Set.mem_setOf_eq, Set.mem_singleton_iff, hasB_eq,
      Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro ⟨i, -, rfl, rfl⟩
      exact hR.one
    · rintro rfl
      exact ⟨0, by decide, rfl, hR.one⟩
  have hle : ∀ h < N, S h ⊆ G₀ := by
    intro h hh
    rw [hG.eq_mset]
    exact subset_of_land (rowOK_spec (hrow h hh)).1
  have hpk : ∀ h < N, ∀ k x, pr h k x → 0 < k ∧ k < N := by
    rintro h hh k x ⟨t, ht, rfl, -⟩
    rw [← testBit_two_pow_sub_two, ← hi, idxAll_bit]
    exact ⟨LO.getD h 0, hmemLO h hh, (idxU_bit _ _).2 ⟨t, ht, rfl⟩⟩
  have hp : ∀ h < N, ∀ k x, pr h k x → x ∉ S h ∧ x * x ∈ S h ∧
      S k = S h ∪ (fun y => y * x) '' S h ∧ S k = S h ∪ (fun y => x * y) '' S h := by
    rintro h hh k x ⟨t, ht, rfl, rfl⟩
    obtain ⟨-, -, hp, -⟩ := rowOK_spec (hrow h hh)
    obtain ⟨h1, h2', h3, h4⟩ := (pairsOK_spec hp t (by have := (hrowLt h hh).1; omega)).1 ht
    have hx := pairX_lt (LO.getD h 0) t
    refine ⟨fun hm => ?_, ?_, ?_, ?_⟩
    · rw [hmem hx, h1] at hm
      exact absurd hm (by decide)
    · rw [← hR.sq hx, hmem (atR_lt _ _)]
      exact h2'
    · change mset elt (latM L _) = _
      rw [h3, mset_lor, mset_imgR_right hR hx]
    · change mset elt (latM L _) = _
      rw [h4, mset_lor, mset_imgR_left hR hx]
  have hpn : ∀ h < N, ∀ k, pn h k → k < N ∧ S h ⊆ S k ∧ (S k).ncard = 2 * (S h).ncard := by
    rintro h hh k ⟨t, ht, hdt, rfl⟩
    obtain ⟨-, -, hp, -⟩ := rowOK_spec (hrow h hh)
    obtain ⟨h1, h2'⟩ := (pairsOK_spec hp t ht).2 hdt
    have hk := (hrowLt h hh).2 t ht
    refine ⟨hk, subset_of_land h1, ?_⟩
    rw [hcard _ hk, hcard h hh, h2']
  have hall : ∀ k, 0 < k → k < N → ∃ h < N, ∃ x, pr h k x := by
    intro k hk0 hk
    have hb : (idxAll LO).testBit k = true := by
      rw [hi, testBit_two_pow_sub_two]
      exact ⟨hk0, hk⟩
    obtain ⟨lo, hlo, hb⟩ := (idxAll_bit k LO).1 hb
    obtain ⟨t, ht, hkt⟩ := (idxU_bit lo k).1 hb
    obtain ⟨h, hh, rfl⟩ := List.getElem_of_mem hlo
    refine ⟨h, hn ▸ hh, _, t, ?_, ?_, rfl⟩
    · rwa [getD_eq_getElem' hh]
    · rwa [getD_eq_getElem' hh]
  have hgn : ∀ h < N, gn h ⊆ S h := by
    rintro h hh _ ⟨t, ht, rfl⟩
    obtain ⟨-, hg, -, -⟩ := rowOK_spec (hrow h hh)
    exact ⟨_, fld127_lt _ _, gensIn_spec hg t ht, rfl⟩
  have hcov : ∀ h < N, ∀ y ∈ G₀, y ∉ S h → (∀ k x, pr h k x → y ∉ S k) →
      (∀ k, pn h k → y ∉ S k) → y * y ∈ S h → ∃ g ∈ gn h, y * g * y⁻¹ ∉ S h := by
    intro h hh y hy hyS hU hUn hyy
    obtain ⟨-, -, -, hc⟩ := rowOK_spec (hrow h hh)
    obtain ⟨x, hx, rfl⟩ := hG.2 y hy
    have hGx : hasB GM x = true := (hG.1 x hx).2 hy
    have hHx : hasB (latM L h) x = false := by
      cases hb : hasB (latM L h) x
      · rfl
      · exact absurd ((hmem hx).2 hb) hyS
    have hUx : hasB (unionU L (LO.getD h 0)) x = false := by
      cases hb : hasB (unionU L (LO.getD h 0)) x
      · rfl
      · obtain ⟨t, ht, hb⟩ := (unionU_bit _ _ _).1 hb
        by_cases hdt : t < desD (LO.getD h 0)
        · exact absurd ((hmem hx).2 hb) (hU _ _ ⟨t, hdt, rfl, rfl⟩)
        · exact absurd ((hmem hx).2 hb) (hUn _ ⟨t, ht, Nat.le_of_not_lt hdt, rfl⟩)
    have hQx : hasB (latM L h) (atR Q x) = true := by
      rw [← hmem (atR_lt _ _), hR.sq hx]
      exact hyy
    have hf := allBelow_spec hc (by decide) x hx
    rw [hGx, hHx, hUx, hQx] at hf
    obtain ⟨t, ht, hw⟩ := witB_spec hf
    refine ⟨_, ⟨t, ht, rfl⟩, fun hm => ?_⟩
    rw [← conjR_elt hR hx (fld127_lt _ _),
      hmem (i := conjR (rowT P x) (rowT C (atR V x)) (genL (latG LG h) t)) (atR_lt _ _), hw] at hm
    exact absurd hm (by decide)
  have hm := lat_math S N G₀ hfin h2 pr pn gn hN hS0 hle hpk hp hpn hall hgn hcov
  refine ⟨fun k hk => ?_, fun K hK => ?_⟩
  · obtain ⟨K, hKG, hK⟩ := hm.1 k hk
    exact ⟨K, hKG, hK ▸ repM_mset hinj _⟩
  · obtain ⟨k, hk, hK⟩ := hm.2 K hK
    exact ⟨k, hk, hK ▸ repM_mset hinj _⟩

end CFSG.KC.G2Three.Sec1T3
