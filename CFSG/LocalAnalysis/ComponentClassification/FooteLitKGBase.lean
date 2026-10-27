module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5 CFSG.ComponentClassification.UnbalancedLayer

@[expose] def FooteKnownQuot (G : Type) [Group G] [Finite G] (m : ℕ) : Prop :=
  ∀ L : Subgroup G, IsFooteComponent L →
    Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin m))

@[expose] def FooteKnownSmall (G : Type) [Group G] [Finite G] : Prop :=
  ∀ L : Subgroup G, IsFooteComponent L → CFSG.pRank 2 ↥(coreActionKernel L) ≤ 1

@[expose] def NoFooteComponent (G : Type) [Group G] [Finite G] : Prop :=
  ∀ L : Subgroup G, ¬ IsFooteComponent L

theorem FooteKnownSmall.of_no {G : Type} [Group G] [Finite G] (h : NoFooteComponent G) :
    FooteKnownSmall G := fun L hL => absurd hL (h L)

theorem foote5KnownGroups_of
    (h9 : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* alternatingGroup (Fin 9)) →
      FooteKnownQuot G 5)
    (h10 : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* alternatingGroup (Fin 10)) →
      FooteKnownQuot G 6)
    (h11 : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* alternatingGroup (Fin 11)) →
      FooteKnownQuot G 7)
    (hJ2 : ∀ (G : Type) [Group G] [Finite G], Blueprint.NativeSporadic.IsSporadic G .J2 →
      FooteKnownQuot G 5)
    (h28 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.LieModel G .PSL 2 2 3 → FooteKnownSmall G)
    (h216 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.LieModel G .PSL 2 2 4 → FooteKnownSmall G)
    (h34 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.LieModel G .PSL 3 2 2 → FooteKnownSmall G)
    (hsz : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.LieModel G .twistedB2 0 2 3 → FooteKnownSmall G)
    (h8 : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* alternatingGroup (Fin 8)) →
      FooteKnownSmall G)
    (hM12 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.NativeSporadic.IsSporadic G .M12 → FooteKnownSmall G)
    (hM22 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.NativeSporadic.IsSporadic G .M22 → FooteKnownSmall G)
    (hM23 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.NativeSporadic.IsSporadic G .M23 → FooteKnownSmall G)
    (hJ1 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.NativeSporadic.IsSporadic G .J1 → FooteKnownSmall G)
    (hJ3 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.NativeSporadic.IsSporadic G .J3 → FooteKnownSmall G)
    (hMcL : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.NativeSporadic.IsSporadic G .McL → FooteKnownSmall G)
    (hLy : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Blueprint.NativeSporadic.IsSporadic G .Ly → FooteKnownSmall G) :
    Foote5KnownGroups := by
  intro G _ _ hs L hL
  refine ⟨fun h => h9 G h L hL, fun h => h10 G h L hL, fun h => h11 G h L hL,
    fun h => hJ2 G h L hL, ?_⟩
  rintro (h | h | h | h | h | h | h | h | h | h | h | h)
  · exact h28 G hs h L hL
  · exact h216 G hs h L hL
  · exact h34 G hs h L hL
  · exact hsz G hs h L hL
  · exact h8 G h L hL
  · exact hM12 G hs h L hL
  · exact hM22 G hs h L hL
  · exact hM23 G hs h L hL
  · exact hJ1 G hs h L hL
  · exact hJ3 G hs h L hL
  · exact hMcL G hs h L hL
  · exact hLy G hs h L hL

theorem even_card_alternatingGroup {m : ℕ} (hm : 4 ≤ m) :
    Even (Nat.card (alternatingGroup (Fin m))) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hm
  rw [hk, show Nat.factorial 4 = 2 * 12 by rfl, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
  exact ⟨6 * k, by ring⟩

theorem nonempty_quot_pPrimeCore_of_mulEquiv {L : Type*} [Group L] [Finite L] {m : ℕ}
    (hm : 5 ≤ m) (e : L ≃* alternatingGroup (Fin m)) :
    Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm)
  have : IsSimpleGroup L := e.isSimpleGroup
  have hbot : pPrimeCore 2 L = ⊥ := by
    have := pPrimeCore_normal (p := 2) (G := L)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 L) with h | h
    · exact h
    · exfalso
      have hc := pPrimeCore_coprime_card (p := 2) (G := L)
      rw [h, card_top, Nat.card_congr e.toEquiv] at hc
      exact Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp hc)
        (even_card_alternatingGroup (by omega))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans e⟩

end CFSG.ComponentClassification.FooteLit.KG
