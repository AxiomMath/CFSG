module

public import Certificates.Data.Kernel.Fi23Q.SubCls
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.Fi23Q

open CFSG.KC.Enum CFSG.KC.Pc3 CFSG.KC.Fi23Q

theorem iteF_iff {p : Prop} [Decidable p] {t : Bool} :
    (if p then t else false) = true ↔ p ∧ t = true := by
  by_cases hp : p <;> simp [hp]

theorem iteT_iff {p : Prop} [Decidable p] {t : Bool} :
    (if p then t else true) = true ↔ (p → t = true) := by
  by_cases hp : p <;> simp [hp]

theorem iteT2_iff {p : Prop} [Decidable p] {t : Bool} :
    (if p then true else t) = true ↔ (¬p → t = true) := by
  by_cases hp : p <;> simp [hp]

theorem anyN_iff {n : ℕ} {f : ℕ → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  unfold anyN
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, CFSG.KS.PK.allN_iff]
  simp only [Bool.not_eq_true', not_forall, Bool.not_eq_false]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h⟩⟩

theorem allT_iff {f : ℕ → Bool} : allT f = true ↔ ∀ i < 81, f (vec3 4 i) = true := by
  unfold allT
  simp only [CFSG.KS.PK.allN_iff, CFSG.KS.PK.strictB_eq]

theorem allE_iff {f : ℕ → Bool} : allE f = true ↔ ∀ i < 243, f (vec3 5 i) = true := by
  unfold allE
  simp only [CFSG.KS.PK.allN_iff, CFSG.KS.PK.strictB_eq]

theorem foldT_eq (f : ℕ → ℕ → ℕ) (s : ℕ) :
    foldT f s = (List.range 81).foldr (fun i acc => f (vec3 4 i) acc) s := by
  unfold foldT
  rw [CFSG.KS.PK.foldN_eq]
  simp only [CFSG.KS.PK.strictN_eq]

theorem foldr_count (l : List ℕ) (p : ℕ → Bool) :
    l.foldr (fun i acc => if p i = true then acc.succ else acc) 0 = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases p a <;> simp

theorem popc_eq (m : ℕ) :
    popc m = ((List.range 81).filter fun i => bitM m (vec3 4 i)).length := by
  unfold popc
  rw [foldT_eq]
  simp only [CFSG.KS.PK.nIf_eq]
  exact foldr_count _ _

theorem cntC_eq (Mt bd : ℕ) :
    cntC Mt bd = ((List.range 243).filter fun i => fixB Mt bd (vec3 5 i)).length := by
  unfold cntC
  rw [CFSG.KS.PK.foldN_eq]
  simp only [CFSG.KS.PK.strictN_eq, CFSG.KS.PK.nIf_eq]
  exact foldr_count _ _

theorem testBit_lor' (u v x : ℕ) : (Nat.lor u v).testBit x = (u.testBit x || v.testBit x) :=
  Nat.testBit_lor u v x

theorem testBit_foldr_if (l : List ℕ) (P : ℕ → Prop) [DecidablePred P] (G : ℕ → ℕ) (x : ℕ) :
    (l.foldr (fun i acc => if P i then Nat.lor acc (G i) else acc) 0).testBit x = true ↔
      ∃ i ∈ l, P i ∧ (G i).testBit x = true := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons]
    by_cases hp : P a
    · rw [if_pos hp, testBit_lor', Bool.or_eq_true, ih]
      simp only [List.mem_cons, exists_eq_or_imp, hp, true_and]
      exact or_comm
    · rw [if_neg hp, ih]
      simp only [List.mem_cons, exists_eq_or_imp, hp, false_and, false_or]

theorem testBit_one_shiftLeft (y x : ℕ) : (Nat.shiftLeft 1 y).testBit x = true ↔ x = y := by
  have e : Nat.shiftLeft 1 y = 2 ^ y := by
    change 1 <<< y = _
    rw [Nat.shiftLeft_eq, one_mul]
  rw [e, Nat.testBit_two_pow]
  simp [eq_comm]

theorem testBit_closM (R m a a2 x : ℕ) :
    (closM R m a a2).testBit x = true ↔ ∃ i < 81, bitM m (vec3 4 i) = true ∧
      (x = vec3 4 i ∨ x = muT R a (vec3 4 i) ∨ x = muT R a2 (vec3 4 i)) := by
  unfold closM
  rw [foldT_eq]
  simp only [CFSG.KS.PK.nIf_eq]
  refine (testBit_foldr_if (List.range 81) (fun i => bitM m (vec3 4 i) = true)
    (fun i => Nat.lor (Nat.shiftLeft 1 (vec3 4 i))
      (Nat.lor (Nat.shiftLeft 1 (muT R a (vec3 4 i))) (Nat.shiftLeft 1 (muT R a2 (vec3 4 i))))) x).trans ?_
  simp only [List.mem_range, testBit_lor', Bool.or_eq_true, testBit_one_shiftLeft]

theorem fixB_iff {Mt bd w : ℕ} :
    fixB Mt bd w = true ↔ ∀ j < f8 bd 0, mC Mt (f8 bd (j + 1)) w = w := by
  unfold fixB
  simp only [CFSG.KS.PK.allN_iff, Nat.beq_eq, Nat.succ_eq_add_one]

theorem commH_iff {R m a : ℕ} :
    commH R m a = true ↔ ∀ i < 81, bitM m (vec3 4 i) = true →
      muT R a (vec3 4 i) = muT R (vec3 4 i) a := by
  unfold commH
  simp only [allT_iff, CFSG.KS.PK.bIf_eq, iteT_iff, Nat.beq_eq]

theorem covE_iff {NPV : List ℕ} {fin : ℕ → Bool} {b w : ℕ} :
    covE NPV fin b w = true ↔ ∃ k < NPV.length, lowV (NPV.getD k 0) 4 = b ∧
      fin (sub3 (Nat.shiftRight (NPV.getD k 0) 8) w) = true := by
  unfold covE
  simp only [anyN_iff, CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.bIf_eq, iteF_iff, Bool.and_eq_true,
    Nat.beq_eq]

theorem shiftLeft4 (i : ℕ) : Nat.shiftLeft i 4 = 16 * i := by
  change i <<< 4 = _
  rw [Nat.shiftLeft_eq]
  ring

theorem one_shiftLeft2 (j : ℕ) : Nat.shiftLeft 1 (Nat.shiftLeft j 1) = 4 ^ j := by
  change 1 <<< (j <<< 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, pow_one, pow_mul']
  norm_num

theorem clsEK_sound {CJ : ℕ} (h : clsEK CJ = true) :
    (∀ i j, 4 ≤ i → i < j → j < 9 → f32 CJ (16 * i + j) = 4 ^ j) ∧
    (∀ k < 4, ∀ j, 4 ≤ j → j < 9 → lowV (f32 CJ (16 * k + j)) 4 = 0) := by
  unfold clsEK at h
  simp only [CFSG.KS.PK.allN_iff, CFSG.KS.PK.bIf_eq, Nat.blt_eq, Nat.ble_eq, shiftLeft4,
    Nat.add_eq, one_shiftLeft2, Nat.beq_eq] at h
  refine ⟨fun i j hi hij hj => ?_, fun k hk j hj hj9 => ?_⟩
  · have := h i (by omega) j hj
    simp only [hij, ↓reduceIte, show ¬ i < 4 by omega, decide_eq_true_eq, Nat.beq_eq] at this
    exact this
  · have := h k (by omega) j hj9
    simp only [show k < j by omega, hk, hj, ↓reduceIte, decide_eq_true_eq, Nat.beq_eq] at this
    exact this

theorem clsRK_sound {PW CJ R : ℕ} (h : clsRK PW CJ R = true) :
    ∀ i < 81, ∀ k < 4, rT R (vec3 4 i) k =
      lowV (mulV PW CJ 9 (vec3 4 i) (Nat.shiftLeft 1 (Nat.shiftLeft k 1))) 4 := by
  unfold clsRK at h
  simp only [allT_iff, CFSG.KS.PK.allN_iff, Nat.beq_eq] at h
  exact h

theorem clsMK_sound {CJ Mt : ℕ} (h : clsMK CJ Mt = true) :
    ∀ i < 81, ∀ c < 5,
      colM Mt (vec3 4 i) c = mT CJ (vec3 4 i) (Nat.shiftLeft 1 (Nat.shiftLeft c 1)) := by
  unfold clsMK at h
  simp only [allT_iff, CFSG.KS.PK.allN_iff, Nat.beq_eq] at h
  exact h

theorem clsLK_sound {R : ℕ} {L : List ℕ} (h : clsLK R L = true) :
    L.getD 0 0 = 1 ∧ ∀ i < L.length, bitM (L.getD i 0) 0 = true ∧
      ∀ ia < 81, bitM (L.getD i 0) (vec3 4 ia) = false →
        muT R (muT R (vec3 4 ia) (vec3 4 ia)) (vec3 4 ia) = 0 →
        commH R (L.getD i 0) (vec3 4 ia) = true →
        ∃ j < L.length, L.getD j 0 =
          closM R (L.getD i 0) (vec3 4 ia) (muT R (vec3 4 ia) (vec3 4 ia)) := by
  unfold clsLK at h
  simp only [CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.bIf_eq, iteF_iff, iteT_iff, iteT2_iff,
    Bool.and_eq_true, CFSG.KS.PK.allN_iff, CFSG.KS.PK.strictB_eq, allT_iff, anyN_iff,
    Nat.beq_eq] at h
  refine ⟨h.1, fun i hi => ⟨(h.2 i hi).1, fun ia hia hb h3 hc => ?_⟩⟩
  exact (h.2 i hi).2 ia hia (by rw [hb]; decide) h3 hc

theorem clsCK_sound {Mt : ℕ} {L B : List ℕ} (h : clsCK Mt L B = true) :
    ∀ i, 1 ≤ i → i < L.length →
      (∀ j < f8 (B.getD i 0) 0, bitM (L.getD i 0) (f8 (B.getD i 0) (j + 1)) = true) ∧
      popc (L.getD i 0) * cntC Mt (B.getD i 0) ≤ 81 := by
  intro i hi1 hi
  unfold clsCK at h
  simp only [CFSG.KS.PK.allN_iff, CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.ble_eq,
    Nat.succ_eq_add_one, Nat.sub_eq, Nat.mul_eq] at h
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  exact h i' (by omega)

theorem clsGK_sound {Mt : ℕ} {NPV B K X : List ℕ} (h : clsGK Mt NPV B K X = true) :
    ∀ i < K.length, K.getD i 0 = 1 → X.getD i 0 < NPV.length ∧
      lowV (NPV.getD (X.getD i 0) 0) 4 = 0 ∧
      fixB Mt (B.getD i 0) (Nat.shiftRight (NPV.getD (X.getD i 0) 0) 8) = true := by
  intro i hi hk
  unfold clsGK at h
  simp only [CFSG.KS.PK.allN_iff, CFSG.KS.PK.bIf_eq, CFSG.KS.PK.bAnd_eq, iteF_iff, iteT_iff,
    Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq] at h
  exact h i hi hk

theorem clsHK_sound {NPV : List ℕ} (h : clsHK NPV = true) :
    ∀ i < 243, vec3 5 i ≠ 0 → ∃ k < NPV.length, lowV (NPV.getD k 0) 4 = 0 ∧
      dot3 (vec3 5 i) (Nat.shiftRight (NPV.getD k 0) 8) = 0 := by
  intro i hi h0
  unfold clsHK at h
  simp only [allE_iff, CFSG.KS.PK.bIf_eq, CFSG.KS.PK.bAnd_eq, iteF_iff, iteT2_iff, anyN_iff,
    Nat.beq_eq, Bool.and_eq_true] at h
  exact h i hi h0

theorem bad2_sound {PW CJ Mt : ℕ} {NPV : List ℕ} {m bd b : ℕ}
    (h : bad2 PW CJ Mt NPV m bd b = true) :
    bitM m b = true ∧ lowV (cubeV PW CJ b) 4 = 0 ∧
      ∀ i < 243, cubeE Mt b (Nat.shiftRight (cubeV PW CJ b) 8) (vec3 5 i) = true →
        ∃ k < NPV.length, lowV (NPV.getD k 0) 4 = b ∧
          fixB Mt bd (sub3 (Nat.shiftRight (NPV.getD k 0) 8) (vec3 5 i)) = true := by
  unfold bad2 at h
  simp only [CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.bIf_eq, iteF_iff, iteT_iff, Bool.and_eq_true,
    CFSG.KS.PK.strictB_eq, Nat.beq_eq, allE_iff] at h
  exact ⟨h.1, h.2.1, fun i hi hc => covE_iff.1 (h.2.2 i hi hc)⟩

theorem clsAK_sound {PW CJ Mt : ℕ} {NPV L B K X : List ℕ}
    (h : clsAK PW CJ Mt NPV L B K X = true) :
    ∀ i < K.length, K.getD i 0 = 2 →
      bad2 PW CJ Mt NPV (L.getD i 0) (B.getD i 0) (X.getD i 0) = true := by
  intro i hi hk
  unfold clsAK at h
  simp only [CFSG.KS.PK.allN_iff, CFSG.KS.PK.bIf_eq, iteT_iff, Nat.beq_eq] at h
  exact h i hi hk

theorem bad3_sound {PW CJ Mt : ℕ} {NPV : List ℕ} {m bd a1 a2 a3 c p : ℕ}
    (h : bad3 PW CJ Mt NPV m bd a1 a2 a3 c p = true) :
    bitM m a1 = true ∧ bitM m a2 = true ∧ bitM m a3 = true ∧ c ≠ 0 ∧ dg c p = 1 ∧ p < 5 ∧
      fixB Mt bd c = true ∧ lowV (cubeV PW CJ a1) 4 = 0 ∧ lowV (cubeV PW CJ a2) 4 = 0 ∧
      lowV (cubeV PW CJ a3) 4 = 0 ∧
      lowV (mulV PW CJ 9 a1 a2) 4 = lowV (mulV PW CJ 9 a2 a1) 4 ∧
      lowV (mulV PW CJ 9 a1 a3) 4 = lowV (mulV PW CJ 9 a3 a1) 4 ∧
      lowV (mulV PW CJ 9 a2 a3) 4 = lowV (mulV PW CJ 9 a3 a2) 4 ∧
      bad3L Mt NPV a1 a2 a3 c p (Nat.shiftRight (cubeV PW CJ a1) 8)
        (Nat.shiftRight (cubeV PW CJ a2) 8) (Nat.shiftRight (cubeV PW CJ a3) 8)
        (sub3 (Nat.shiftRight (mulV PW CJ 9 a1 a2) 8) (Nat.shiftRight (mulV PW CJ 9 a2 a1) 8))
        (sub3 (Nat.shiftRight (mulV PW CJ 9 a1 a3) 8) (Nat.shiftRight (mulV PW CJ 9 a3 a1) 8))
        (sub3 (Nat.shiftRight (mulV PW CJ 9 a2 a3) 8) (Nat.shiftRight (mulV PW CJ 9 a3 a2) 8))
        = true := by
  unfold bad3 cubeK commK at h
  simp only [CFSG.KS.PK.bAnd_eq, CFSG.KS.PK.bIf_eq, iteF_iff, Bool.and_eq_true,
    CFSG.KS.PK.strictB_eq, Nat.beq_eq, Bool.not_eq_true', Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, hc, hp, hp5, hf, y1, y2, y3, u12, u13, u23, hL⟩ := h
  refine ⟨h1, h2, h3, ?_, hp, hp5, hf, y1, y2, y3, u12, u13, u23, hL⟩
  intro e
  rw [e] at hc
  exact absurd hc (by decide)

theorem bad3L_sound {Mt : ℕ} {NPV : List ℕ} {a1 a2 a3 c p t1 t2 t3 g12 g13 g23 : ℕ}
    (h : bad3L Mt NPV a1 a2 a3 c p t1 t2 t3 g12 g13 g23 = true) :
    ∀ i1 < 243, ∀ i2 < 243, ∀ i3 < 243,
      dg (vec3 5 i1) p = 0 → dg (vec3 5 i2) p = 0 → dg (vec3 5 i3) p = 0 →
      cubeE Mt a1 t1 (vec3 5 i1) = true → cubeE Mt a2 t2 (vec3 5 i2) = true →
      cubeE Mt a3 t3 (vec3 5 i3) = true →
      commE Mt a1 a2 g12 (vec3 5 i1) (vec3 5 i2) = true →
      commE Mt a1 a3 g13 (vec3 5 i1) (vec3 5 i3) = true →
      commE Mt a2 a3 g23 (vec3 5 i2) (vec3 5 i3) = true →
      covE NPV (inC1 c) a1 (vec3 5 i1) = true ∨ covE NPV (inC1 c) a2 (vec3 5 i2) = true ∨
        covE NPV (inC1 c) a3 (vec3 5 i3) = true := by
  intro i1 h1 i2 h2 i3 h3 p1 p2 p3 c1 c2 c3 m12 m13 m23
  unfold bad3L at h
  simp only [allE_iff, CFSG.KS.PK.bIf_eq, CFSG.KS.PK.bAnd_eq, iteT_iff, iteF_iff,
    Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true', and_imp] at h
  by_cases v1 : covE NPV (inC1 c) a1 (vec3 5 i1) = true
  · exact Or.inl v1
  by_cases v2 : covE NPV (inC1 c) a2 (vec3 5 i2) = true
  · exact Or.inr (Or.inl v2)
  refine Or.inr (Or.inr ?_)
  simp only [Bool.not_eq_true] at v1 v2
  exact h i1 h1 p1 c1 v1 i2 h2 p2 c2 m12 v2 i3 h3 p3 c3 m13 m23

theorem clsBK_sound {PW CJ Mt : ℕ} {NPV L B K D3 : List ℕ}
    (h : clsBK PW CJ Mt NPV L B K D3 = true) :
    ∀ i < K.length, K.getD i 0 = 3 →
      bad3 PW CJ Mt NPV (L.getD i 0) (B.getD i 0) (D3.getD 0 0) (D3.getD 1 0) (D3.getD 2 0)
        (D3.getD 3 0) (D3.getD 4 0) = true := by
  intro i hi hk
  unfold clsBK at h
  simp only [CFSG.KS.PK.allN_iff, CFSG.KS.PK.bIf_eq, iteT_iff, Nat.beq_eq] at h
  exact h i hi hk

theorem clsKK_sound {L K : List ℕ} (h : clsKK L K = true) :
    K.length = L.length ∧ K.getD 0 0 = 0 ∧
      ∀ i, 1 ≤ i → i < K.length → 1 ≤ K.getD i 0 ∧ K.getD i 0 ≤ 3 := by
  unfold clsKK at h
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.allN_iff,
    Nat.ble_eq, Nat.succ_eq_add_one, Nat.sub_eq] at h
  refine ⟨h.1, h.2.1, fun i hi1 hi => ?_⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  exact h.2.2 i' (by omega)

end CFSG.KS.Fi23Q

end
