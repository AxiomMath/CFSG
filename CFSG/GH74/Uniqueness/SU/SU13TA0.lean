module

public import CFSG.GH74.Uniqueness.SU.KInputs

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Subgroup

structure TwoCover {H : Type} [Group H] {n : ℕ} (π : H →* alternatingGroup (Fin n)) : Prop where
  surj : Function.Surjective π
  ker_le_center : π.ker ≤ center H
  card_ker : Nat.card π.ker = 2
  perfect : Group.IsPerfect H

theorem TwoCover.exists_of_isTwoAlt {H : Type} [Group H] {n : ℕ} (hH : K.IsTwoAlt H n) :
    ∃ π : H →* alternatingGroup (Fin n), TwoCover π := by
  obtain ⟨⟨hperf, -, -⟩, -, hc, ⟨e⟩⟩ := hH
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (center H))).ker = center H := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : e ((QuotientGroup.mk' (center H)) x) = 1 := hx
      exact (QuotientGroup.eq_one_iff x).mp ((map_eq_one_iff e e.injective).mp h1)
    · intro hx
      have h1 : (QuotientGroup.mk' (center H)) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      show e ((QuotientGroup.mk' (center H)) x) = 1
      rw [h1, map_one]
  exact ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center H)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), hker.le, by rw [hker]; exact hc, hperf⟩

end CFSG.GH74.Uniqueness.SU.SU13.TA
