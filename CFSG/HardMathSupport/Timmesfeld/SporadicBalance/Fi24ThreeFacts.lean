module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.Sporadic.Fi24.OctadAction

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Sporadic.Th CFSG.Perm CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [local instance] CFSG.Sporadic.Fi24.rAction


structure FixFacts (w : List ℕ) (y : ℕ) : Prop where
  letters_lt : ∀ l ∈ w, l < letters.size
  pow3 : wordElt w ^ 3 = 1
  ne_one : wordElt w ≠ 1
  fix0 : ∀ t < 3, idx 306936 (wordElt w) chainBase[t]! = chainBase[t]!
  y_lt : y < 306936
  fixy : idx 306936 (wordElt w) y = y
  sep : ∀ k k' : Fin 306936, wordElt w • k = k → wordElt w • k' = k' → k ≠ k' →
    cls k * cls k' = cls k' * cls k → ∃ t : Fin 306936, wordElt w • t = t ∧
      ((cls t * cls k = cls k * cls t ∧ cls t * cls k' ≠ cls k' * cls t) ∨
        (cls t * cls k ≠ cls k * cls t ∧ cls t * cls k' = cls k' * cls t))
  p1 : ∀ k : Fin 306936, wordElt w • k = k → ∃ t : Fin 306936, wordElt w • t = t ∧
    cls k * cls t ≠ cls t * cls k
  gens : ∀ k : Fin 306936, wordElt w • k ≠ k →
    cls k * cls (wordElt w • k) = cls (wordElt w • k) * cls k →
    ∃ d e : Fin 306936, wordElt w • d = d ∧ wordElt w • e = e ∧
      (cls d * cls e) • k ≠ k ∧ (cls d * cls e) • k ≠ wordElt w • k ∧
      (cls d * cls e) • k ≠ wordElt w • (wordElt w • k)

@[expose] def InQ (s : J) (x : Fin 306936) : Prop := cls x * cls (s • x) = cls (s • x) * cls x

@[expose] noncomputable def uR (s : J) (x : Fin 306936) : R :=
  cls x * cls (s • x) * cls (s • (s • x))

structure FreeFacts (w : List ℕ) (d0 : Fin 306936) : Prop where
  letters_lt : ∀ l ∈ w, l < letters.size
  pow3 : wordElt w ^ 3 = 1
  fpf : ∀ k : Fin 306936, wordElt w • k ≠ k
  qd0 : InQ (wordElt w) d0
  orbit : ∃ H : Subgroup R, (∀ g ∈ H, g * jR (wordElt w) = jR (wordElt w) * g) ∧
    ∀ x : Fin 306936, InQ (wordElt w) x → ∃ g ∈ H, g • d0 = x
  crit : ∀ x : Fin 306936, InQ (wordElt w) x → x ≠ d0 → x ≠ wordElt w • d0 →
    x ≠ wordElt w • (wordElt w • d0) → x.val ≤ (wordElt w • x).val →
    x.val ≤ (wordElt w • (wordElt w • x)).val →
    3 ∣ orderOf (uR (wordElt w) d0 * uR (wordElt w) x) ∨
      ∃ k : Fin 306936, InQ (wordElt w) k ∧ 3 ∣ orderOf (uR (wordElt w) d0 * uR (wordElt w) x *
        uR (wordElt w) k * uR (wordElt w) d0 * uR (wordElt w) x * uR (wordElt w) k)
  base : ∀ i < 6, ∃ a b : Fin 306936, InQ (wordElt w) a ∧ InQ (wordElt w) b ∧
    (cls a • b).val = chainBase[i]!
  bgen : ∃ k l : Fin 306936, InQ (wordElt w) k ∧ InQ (wordElt w) l ∧ ∀ x : Fin 306936,
    InQ (wordElt w) x → (uR (wordElt w) k * uR (wordElt w) l) • x ≠ x ∧
      (uR (wordElt w) k * uR (wordElt w) l) • x ≠ wordElt w • x ∧
      (uR (wordElt w) k * uR (wordElt w) l) • x ≠ wordElt w • (wordElt w • x)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

end
