module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAltOrder
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAltArith

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open TauCeti

theorem two_mul_card_alt_fin (n : ℕ) (hn : 5 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [two_mul_nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

theorem altTypeExcl_holds : AltTypeExcl := by
  intro n hn
  refine ⟨?_, ?_, ?_⟩
  · rintro m d ⟨q, hq, hd | hd⟩
    · refine ⟨fun e => ?_⟩
      have hm : 4 ≤ m := by
        obtain ⟨d, hv⟩ := d
        simp only at hd
        subst hd
        exact four_le_of_valid_D hv
      have h := two_mul_card_alt_fin n hn
      rw [Nat.card_congr e.toEquiv, card_lie_typeD_two m d q hq hd] at h
      exact factorial_ne_two_mul_orth hm hn (Or.inl rfl) (by rw [← h]; rfl)
    · refine ⟨fun e => ?_⟩
      have hm : 4 ≤ m := by
        obtain ⟨d, hv⟩ := d
        simp only at hd
        subst hd
        exact four_le_of_valid_twistedD hv
      have h := two_mul_card_alt_fin n hn
      rw [Nat.card_congr e.toEquiv, card_lie_twistedD_two m d q hq hd] at h
      exact factorial_ne_two_mul_orth hm hn (Or.inr rfl) (by rw [← h]; rfl)
  · rintro d ⟨q, hq, hd⟩
    refine ⟨fun e => ?_⟩
    have h := two_mul_card_alt_fin n hn
    rw [Nat.card_congr e.toEquiv, card_lie_twistedA_three_two d q hq hd] at h
    exact factorial_ne_51840 hn h.symm
  · rintro k hk ⟨e⟩
    exact eq_of_two_mul_card_alt hn hk (Nat.card_congr e.toEquiv)

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
