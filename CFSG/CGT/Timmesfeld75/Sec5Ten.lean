module

public import CFSG.CGT.Timmesfeld75.Sec5NineExcl

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def AltCoverInput : Prop :=
  ∀ (k : ℕ), (k = 6 ∨ k = 7) → ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ →
    ∀ (Z : Subgroup Y) [Z.Normal], Z ≤ Subgroup.center Y →
      Nonempty (Y ⧸ Z ≃* alternatingGroup (Fin k)) → (∃ y : Y, y ∉ Z ∧ y * y = 1) →
        Nat.card Z ∣ 3

theorem card_center_dvd_three_of_ident59 (hAlt : AltCoverInput) {Y : Type} [Group Y] [Finite Y]
    {E : Subgroup Y} (hO : Ident59Out Y E) {k : ℕ} (hk : k = 6 ∨ k = 7)
    (hK : Nonempty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin k))) :
    Nat.card (Subgroup.center Y) ∣ 3 := by
  have hE1 : E ≠ ⊥ := by
    intro h
    have := hO.four_le
    rw [h] at this
    simp at this
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine hAlt k hk Y hO.perfect (Subgroup.center Y) le_rfl hK ⟨y, fun hyZ => hy1' ?_,
    elemAbelian_mul_self hO.wc.1 hy⟩
  have : y ∈ E ⊓ Subgroup.center Y := ⟨hy, hyZ⟩
  rw [hO.inf_center, Subgroup.mem_bot] at this
  exact this

end CFSG.CGT.Timmesfeld75
