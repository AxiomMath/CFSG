module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisAlg

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

open Module CFSG.RankThree.PartOne.KCLinPlane

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {p : ℕ} [NeZero p] {f : ZMod p → Module.End K V} {t ti : Module.End K V} {c₀ : K}

namespace HeisData

variable (H : HeisData p f t ti c₀)

include H

theorem finrank_range_succ_le (j : ZMod p) :
    finrank K (LinearMap.range (f j)) ≤ finrank K (LinearMap.range (f (j + 1))) := by
  let φ : LinearMap.range (f j) →ₗ[K] LinearMap.range (f (j + 1)) :=
    (t.comp (LinearMap.range (f j)).subtype).codRestrict _ (by
      rintro ⟨_, v, rfl⟩
      have := congrArg (fun g : Module.End K V => g v) (H.shift j)
      simp only [Module.End.mul_apply] at this
      exact ⟨t v, by simpa using this.symm⟩)
  refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
  intro x y hxy
  have h1 : t (x : V) = t (y : V) := congrArg Subtype.val hxy
  have h2 : (x : V) = (y : V) := by
    have := congrArg ti h1
    have e : ∀ z : V, ti (t z) = z := fun z => by
      simpa [Module.End.mul_apply] using congrArg (fun g : Module.End K V => g z) H.ti_t
    rwa [e, e] at this
  exact Subtype.ext h2

theorem finrank_range_pred_le (j : ZMod p) :
    finrank K (LinearMap.range (f (j + 1))) ≤ finrank K (LinearMap.range (f j)) := by
  let φ : LinearMap.range (f (j + 1)) →ₗ[K] LinearMap.range (f j) :=
    (ti.comp (LinearMap.range (f (j + 1))).subtype).codRestrict _ (by
      rintro ⟨_, v, rfl⟩
      have := congrArg (fun g : Module.End K V => g (ti v)) (H.shift j)
      simp only [Module.End.mul_apply] at this
      have e : t (ti v) = v := by
        simpa [Module.End.mul_apply] using congrArg (fun g : Module.End K V => g v) H.t_ti
      rw [e] at this
      exact ⟨ti v, by
        change f j (ti v) = ti (f (j + 1) v)
        have h2 := congrArg ti this
        have e2 : ∀ z : V, ti (t z) = z := fun z => by
          simpa [Module.End.mul_apply] using congrArg (fun g : Module.End K V => g z) H.ti_t
        rwa [e2] at h2⟩)
  refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
  intro x y hxy
  have h1 : ti (x : V) = ti (y : V) := congrArg Subtype.val hxy
  have h2 : (x : V) = (y : V) := by
    have := congrArg t h1
    have e : ∀ z : V, t (ti z) = z := fun z => by
      simpa [Module.End.mul_apply] using congrArg (fun g : Module.End K V => g z) H.t_ti
    rwa [e, e] at this
  exact Subtype.ext h2

theorem finrank_range_succ (j : ZMod p) :
    finrank K (LinearMap.range (f (j + 1))) = finrank K (LinearMap.range (f j)) :=
  le_antisymm (H.finrank_range_pred_le j) (H.finrank_range_succ_le j)

theorem finrank_range_nat (k : ℕ) :
    finrank K (LinearMap.range (f (k : ZMod p))) = finrank K (LinearMap.range (f 0)) := by
  induction k with
  | zero => rw [Nat.cast_zero]
  | succ k ih =>
    rw [Nat.cast_succ, H.finrank_range_succ, ih]

theorem finrank_range (j : ZMod p) :
    finrank K (LinearMap.range (f j)) = finrank K (LinearMap.range (f 0)) := by
  have := H.finrank_range_nat j.val
  rwa [ZMod.natCast_zmod_val] at this

theorem finrank_eq_mul : finrank K V = p * finrank K (LinearMap.range (f 0)) := by
  have h1 := (blockDecomp f H.idem H.orth H.sum).finrank_eq
  rw [h1, Module.finrank_pi_fintype]
  simp only [H.finrank_range]
  simp [ZMod.card]

end HeisData

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis
