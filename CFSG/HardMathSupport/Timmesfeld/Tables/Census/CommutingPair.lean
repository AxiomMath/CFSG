module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

@[expose] def pairHom {X : Type*} [Group X] (A B : X) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hAB : A * B = B * A) : Multiplicative (ZMod 3 × ZMod 3) →* X where
  toFun x := A ^ (Multiplicative.toAdd x).1.val * B ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' x y := by
    have hc : ∀ i j : ℕ, B ^ j * A ^ i = A ^ i * B ^ j := fun i j =>
      ((Commute.pow_pow (show Commute A B from hAB) i j).eq).symm
    have hv : ∀ (u : ZMod 3) (g : X), g ^ 3 = 1 → ∀ w : ZMod 3, g ^ (u + w).val =
        g ^ u.val * g ^ w.val := fun u g hg w => by
      rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]
    induction x using Multiplicative.rec with
    | ofAdd x =>
      induction y using Multiplicative.rec with
      | ofAdd y =>
        obtain ⟨a, b⟩ := x
        obtain ⟨c, d⟩ := y
        show A ^ (a + c).val * B ^ (b + d).val = (A ^ a.val * B ^ b.val) * (A ^ c.val * B ^ d.val)
        rw [hv a A hA c, hv b B hB d]
        calc A ^ a.val * A ^ c.val * (B ^ b.val * B ^ d.val)
            = A ^ a.val * (A ^ c.val * B ^ b.val) * B ^ d.val := by group
          _ = A ^ a.val * (B ^ b.val * A ^ c.val) * B ^ d.val := by rw [← hc c.val b.val]
          _ = _ := by group

theorem pairHom_apply {X : Type*} [Group X] (A B : X) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hAB : A * B = B * A) (i j : ZMod 3) :
    pairHom A B hA hB hAB (Multiplicative.ofAdd (i, j)) = A ^ i.val * B ^ j.val := rfl

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
