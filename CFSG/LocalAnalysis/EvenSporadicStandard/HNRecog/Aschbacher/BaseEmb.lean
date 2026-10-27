module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem ofAdd_one_ne_one :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by
  decide

def A5WrTwo.baseEmb : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* A5WrTwo where
  toFun p := ⟨fun i => if i = 1 then p.1 else p.2, 1⟩
  map_one' := by
    apply RegularWreathProduct.ext
    · funext i
      by_cases h : i = 1 <;> simp [h]
    · rfl
  map_mul' := by
    intro p q
    apply RegularWreathProduct.ext
    · funext i
      by_cases h : i = 1 <;> simp [h]
    · simp [RegularWreathProduct.mul_def]

theorem A5WrTwo.baseEmb_injective : Function.Injective A5WrTwo.baseEmb := by
  intro p q h
  have h1 : p.1 = q.1 := by
    simpa [A5WrTwo.baseEmb] using congrArg (fun g : A5WrTwo => g.left 1) h
  have h2 : p.2 = q.2 := by
    simpa [A5WrTwo.baseEmb, ofAdd_one_ne_one] using
      congrArg (fun g : A5WrTwo => g.left (Multiplicative.ofAdd 1)) h
  exact Prod.ext h1 h2

theorem A5WrTwo.range_baseEmb : A5WrTwo.baseEmb.range = commutator A5WrTwo := by
  rw [A5WrTwo.commutator_eq_ker]
  apply le_antisymm
  · rintro g ⟨p, rfl⟩
    exact MonoidHom.mem_ker.mpr rfl
  · intro g hg
    have hgright : g.right = 1 := hg
    refine MonoidHom.mem_range.mpr
      ⟨(g.left 1, g.left (Multiplicative.ofAdd 1)), ?_⟩
    apply RegularWreathProduct.ext
    · change (fun i => if i = 1 then g.left 1 else g.left (Multiplicative.ofAdd 1)) =
        g.left
      funext q
      rcases coord_cases q with rfl | rfl <;> simp [ofAdd_one_ne_one]
    · change (1 : Multiplicative (ZMod 2)) = g.right
      rw [hgright]

theorem A5WrTwo.swap_mul_baseEmb_mul_inv (x y : alternatingGroup (Fin 5)) :
    (⟨1, Multiplicative.ofAdd 1⟩ : A5WrTwo) * A5WrTwo.baseEmb (x, y) *
      (⟨1, Multiplicative.ofAdd 1⟩ : A5WrTwo)⁻¹ = A5WrTwo.baseEmb (y, x) := by
  have hσ2 : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) *
      (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) = 1 := by decide
  have hσinv : (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹ =
      Multiplicative.ofAdd 1 := inv_eq_of_mul_eq_one_right hσ2
  apply RegularWreathProduct.ext
  · funext q
    rcases coord_cases q with rfl | rfl <;>
      simp [A5WrTwo.baseEmb, RegularWreathProduct.mul_def, hσ2, hσinv,
        ofAdd_one_ne_one]
  · simp [A5WrTwo.baseEmb, RegularWreathProduct.mul_def, hσ2, hσinv]

end CFSG.EvenSporadicStandard.HNRecog
