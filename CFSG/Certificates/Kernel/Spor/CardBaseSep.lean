module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.KS.CardSep

theorem eq_of_base {n N : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} (hcard : Nat.card H = N)
    {ε : ℕ → Equiv.Perm (Fin n)} (hε : ∀ i < N, ε i ∈ H) {B : List (Fin n)}
    (hkey : ∀ i < N, ∀ j < N, (∀ b ∈ B, ε i b = ε j b) → i = j) {x y : Equiv.Perm (Fin n)}
    (hx : x ∈ H) (hy : y ∈ H) (hxy : ∀ b ∈ B, x b = y b) : x = y := by
  let f : Fin N → H := fun i => ⟨ε i, hε i i.2⟩
  have hinj : Function.Injective f := fun i j e => by
    have e' : ε i = ε j := congrArg Subtype.val e
    exact Fin.ext (hkey i i.2 j j.2 fun b _ => by rw [e'])
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨a, ha⟩ := hbij.2 ⟨x, hx⟩
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
  have hax : ε a = x := congrArg Subtype.val ha
  have hcy : ε c = y := congrArg Subtype.val hc
  have e : a = c := Fin.ext (hkey a a.2 c c.2 fun b hb => by rw [hax, hcy]; exact hxy b hb)
  rw [← hax, ← hcy, e]

end CFSG.KS.CardSep

end
