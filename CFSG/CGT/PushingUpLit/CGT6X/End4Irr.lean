module

public import CFSG.CGT.PushingUpLit.CGT6X.End3Irr

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6X.End3

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem commV_conjClosure_eq_top (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) :
    commV (CGT6.conjClosure Y G) = ⊤ := by
  have hne : commV Y ≠ ⊥ := fun h => (simpleQuot_of_cfg hV cfg).1 (by rw [h]; simp)
  have hinv : GInv (CGT6.conjClosure Y G) (commV (CGT6.conjClosure Y G)) :=
    fun l hl a ha => CGT6.commV_invariant hl ha
  rcases irreducible_of_cfg hV cfg hinv with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff, ← h]
    exact CGT6.commV_mono CGT6.le_conjClosure
  · exact h

theorem fix_conjClosure_trivial (hV : ∀ v : V, v ^ 2 = 1) (cfg : EndCfg4 G T Y) :
    ∀ w : V, (∀ x : ↥(CGT6.conjClosure Y G), (x : MulAut V) w = w) → w = 1 := by
  intro w hw
  have hne : commV Y ≠ ⊥ := fun h => (simpleQuot_of_cfg hV cfg).1 (by rw [h]; simp)
  have hinv : GInv (CGT6.conjClosure Y G) (fixV (CGT6.conjClosure Y G)) :=
    fun l hl a ha => by rw [show l a = a from ha l hl]; exact ha
  rcases irreducible_of_cfg hV cfg hinv with h | h
  · have : w ∈ fixV (CGT6.conjClosure Y G) := fun x hx => hw ⟨x, hx⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  · exfalso
    apply hne
    rw [eq_bot_iff]
    refine (CGT6.commV_mono (CGT6.le_conjClosure (Y := Y) (Xt := G))).trans ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    have hv : v ∈ fixV (CGT6.conjClosure Y G) := by rw [h]; exact Subgroup.mem_top v
    show x v * v⁻¹ ∈ (⊥ : Subgroup V)
    rw [Subgroup.mem_bot, show x v = v from hv x hx, mul_inv_cancel]

end CFSG.CGT.PushingUpLit.CGT6X.End4
