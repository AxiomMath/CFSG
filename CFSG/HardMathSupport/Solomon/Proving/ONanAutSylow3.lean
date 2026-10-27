module

public import CFSG.HardMathSupport.Solomon.Proving.Fi22AutTables

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.ComponentClassification.OuterAutomorphisms

theorem onan_card_mulAut_three_part
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hsimp : IsSimpleGroup (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group)
    (S : Type) [Group S] [Finite S]
    (hS : Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group)) :
    ∃ m : ℕ, Nat.card (MulAut S) = 3 ^ 4 * m ∧ ¬ 3 ∣ m := by
  obtain ⟨e⟩ := hS
  have hsimpS : IsSimpleGroup S := by
    have := hsimp
    exact MulEquiv.isSimpleGroup e
  have hcardS : Nat.card S = 460815505920 := by
    rw [Nat.card_congr e.toEquiv]
    exact (hOrd TauCeti.SporadicName.ONan).trans rfl
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    apply fi22_exists_noncomm
    rw [hcardS]
    norm_num
  have hcenter : Subgroup.center S = ⊥ := fi22_center_eq_bot hnab
  have hout : Nat.card (Outer S) ≤ 2 :=
    hOut S hsimpS hnab TauCeti.SporadicName.ONan ⟨e⟩
  have hmul : Nat.card (MulAut S) = Nat.card S * Nat.card (Outer S) :=
    fi22_card_mulAut hcenter
  have hcpos : 0 < Nat.card (Outer S) := Nat.card_pos
  have hc12 : Nat.card (Outer S) = 1 ∨ Nat.card (Outer S) = 2 := by omega
  rcases hc12 with h | h
  · refine ⟨5689080320, ?_, ?_⟩
    · rw [hmul, hcardS, h]
      norm_num
    · norm_num
  · refine ⟨2 * 5689080320, ?_, ?_⟩
    · rw [hmul, hcardS, h]
      norm_num
    · norm_num

end CFSG.HardMathSupport.Solomon.Proving

end
