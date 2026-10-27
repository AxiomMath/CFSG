module

public import CFSG.LargeExtraspecial.A2ModOrd
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LargeExtraspecial.A2Mod

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Timmesfeld

namespace Ord

variable {X : Type} [Group X]

theorem statedClassicalModel_of_lieModel {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel X t n p f) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem card_of_lieModel_PSL {m : ℕ} (h : LieModel X .PSL m 2 1) :
    3 ≤ m ∧ Nat.card X = ordA (m - 1) 2 := by
  have hc := statedClassicalModel_of_lieModel (by decide) h
  obtain ⟨-, -, hm, hne, -⟩ := hc.1
  refine ⟨?_, (card_statedClassicalModel_two hc).1 rfl⟩
  by_contra hlt
  exact hne (by simp only [Prod.mk.injEq]; omega)

theorem card_of_lieModel_PSp {m : ℕ} (h : LieModel X .PSp m 2 1) :
    3 ≤ m ∧ Nat.card X = ordBC m 2 := by
  have hc := statedClassicalModel_of_lieModel (by decide) h
  obtain ⟨-, -, hm, hne⟩ := hc.1
  refine ⟨?_, (card_statedClassicalModel_two hc).2.2.1 rfl⟩
  by_contra hlt
  exact hne (by simp only [Prod.mk.injEq]; omega)

theorem card_of_lieModel_POmegaPlus {m : ℕ} (h : LieModel X .POmegaPlus m 2 1) :
    4 ≤ m ∧ Nat.card X = ordD m 2 := by
  have hc := statedClassicalModel_of_lieModel (by decide) h
  exact ⟨hc.1.2.2, (card_statedClassicalModel_two hc).2.2.2.1 rfl⟩

theorem card_of_lieModel_POmegaMinus {m : ℕ} (h : LieModel X .POmegaMinus m 2 1) :
    4 ≤ m ∧ Nat.card X = ordTwistedD m 2 := by
  have hc := statedClassicalModel_of_lieModel (by decide) h
  exact ⟨hc.1.2.2, (card_statedClassicalModel_two hc).2.2.2.2 rfl⟩

theorem card_of_lieModel_POmega {m : ℕ}
    (h : LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1) :
    4 ≤ m ∧ (Nat.card X = ordD m 2 ∨ Nat.card X = ordTwistedD m 2) := by
  rcases h with h | h
  · exact ⟨(card_of_lieModel_POmegaPlus h).1, Or.inl (card_of_lieModel_POmegaPlus h).2⟩
  · exact ⟨(card_of_lieModel_POmegaMinus h).1, Or.inr (card_of_lieModel_POmegaMinus h).2⟩

theorem card_of_lieModel_PSU33 (h : LieModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three (h.statedClassicalModel (by decide))

theorem lieModel_PSL_false_of_POmega {m k : ℕ} (h : LieModel X .PSL m 2 1)
    (h' : LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1) : False := by
  obtain ⟨hm, hX⟩ := card_of_lieModel_PSL h
  obtain ⟨hk, hX' | hX'⟩ := card_of_lieModel_POmega h'
  · exact ordA_ne_ordD (n := m - 1) (by omega) hk (hX.symm.trans hX')
  · exact ordA_ne_ordTwistedD (n := m - 1) (by omega) hk (hX.symm.trans hX')

theorem lieModel_PSp_false_of_POmega {m k : ℕ} (h : LieModel X .PSp m 2 1)
    (h' : LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1) : False := by
  obtain ⟨hm, hX⟩ := card_of_lieModel_PSp h
  obtain ⟨hk, hX' | hX'⟩ := card_of_lieModel_POmega h'
  · exact ordBC_ne_ordD (by omega) (by omega) (hX.symm.trans hX')
  · exact ordBC_ne_ordTwistedD (by omega) (by omega) (hX.symm.trans hX')

theorem eq_of_lieModel_POmega {m k : ℕ}
    (h : LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1)
    (h' : LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1) : m = k := by
  obtain ⟨hm, hX | hX⟩ := card_of_lieModel_POmega h <;>
    obtain ⟨hk, hX' | hX'⟩ := card_of_lieModel_POmega h'
  · exact eq_of_ordD_eq_ordD (by omega) (by omega) (hX.symm.trans hX')
  · exact eq_of_ordD_eq_ordTwistedD (by omega) (by omega) (hX.symm.trans hX')
  · exact eq_of_ordTwistedD_eq_ordD (by omega) (by omega) (hX.symm.trans hX')
  · exact eq_of_ordTwistedD_eq_ordTwistedD (by omega) (by omega) (hX.symm.trans hX')

theorem twelve_thousand_lt_card_of_lieModel_classical {m : ℕ}
    (h : (4 ≤ m ∧ LieModel X .PSL m 2 1) ∨ LieModel X .PSp m 2 1 ∨ LieModel X .POmegaPlus m 2 1 ∨
      LieModel X .POmegaMinus m 2 1) : 12096 < Nat.card X := by
  rcases h with ⟨hm, h⟩ | h | h | h
  · rw [(card_of_lieModel_PSL h).2]
    exact twelve_thousand_lt_ordA (by omega)
  · obtain ⟨hm, hX⟩ := card_of_lieModel_PSp h
    rw [hX]
    exact twelve_thousand_lt_ordBC hm
  · obtain ⟨hm, hX⟩ := card_of_lieModel_POmegaPlus h
    rw [hX]
    exact twelve_thousand_lt_ordD hm
  · obtain ⟨hm, hX⟩ := card_of_lieModel_POmegaMinus h
    rw [hX]
    exact twelve_thousand_lt_ordTwistedD hm

theorem chevalleyExceptionalModel_of_lieModel {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : LieModel X t n p f) :
    ChevalleyExceptionalModel X t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

section Exceptional

theorem card_of_lieModel_F4 {n : ℕ} (h : LieModel X .F4 n 2 1) : Nat.card X = ordF4 2 :=
  card_chevalleyExceptionalModel_two (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_E6 {n : ℕ} (h : LieModel X .E6 n 2 1) : Nat.card X = ordE6 2 :=
  card_chevalleyExceptionalModel_two (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_twistedE6 {n : ℕ} (h : LieModel X .twistedE6 n 2 1) :
    Nat.card X = ordTwistedE6 2 :=
  card_chevalleyExceptionalModel_two (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_E7 {n : ℕ} (h : LieModel X .E7 n 2 1) : Nat.card X = ordE7 2 :=
  card_chevalleyExceptionalModel_two (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_E8 {n : ℕ} (h : LieModel X .E8 n 2 1) : Nat.card X = ordE8 2 :=
  card_chevalleyExceptionalModel_two (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_trialityD4 {n : ℕ} (h : LieModel X .trialityD4 n 2 1) :
    Nat.card X = 211341312 := by
  rw [← ordTrialityD4_two]
  exact card_chevalleyExceptionalModel_two (chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem card_of_lieModel_exceptional {τ : StatedLieTag}
    (hτ : τ ∈ ({.F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag)) {n : ℕ}
    (h : LieModel X τ n 2 1) :
    Nat.card X = ordF4 2 ∨ Nat.card X = ordE6 2 ∨ Nat.card X = ordTwistedE6 2 ∨
      Nat.card X = ordE7 2 ∨ Nat.card X = ordE8 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (card_of_lieModel_F4 h)
  · exact Or.inr (Or.inl (card_of_lieModel_E6 h))
  · exact Or.inr (Or.inr (Or.inl (card_of_lieModel_twistedE6 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (card_of_lieModel_E7 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (card_of_lieModel_E8 h))))

theorem lieModel_POmega_false_of_exceptional {k n : ℕ} {τ : StatedLieTag}
    (hτ : τ ∈ ({.F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (h : LieModel X .POmegaPlus k 2 1 ∨ LieModel X .POmegaMinus k 2 1)
    (h' : LieModel X τ n 2 1) : False := by
  obtain ⟨hk, hX | hX⟩ := card_of_lieModel_POmega h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := ordD_ne_exceptional (show 1 ≤ k by omega)
    rcases card_of_lieModel_exceptional hτ h' with e | e | e | e | e <;> rw [hX] at e
    exacts [h1 e, h2 e, h3 e, h4 e, h5 e]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := ordTwistedD_ne_exceptional (show 1 ≤ k by omega)
    rcases card_of_lieModel_exceptional hτ h' with e | e | e | e | e <;> rw [hX] at e
    exacts [h1 e, h2 e, h3 e, h4 e, h5 e]

theorem lieModel_PSL_false_of_exceptional {m n : ℕ} {τ : StatedLieTag}
    (hτ : τ ∈ ({.F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (h : LieModel X .PSL m 2 1) (h' : LieModel X τ n 2 1) : False := by
  obtain ⟨hm, hX⟩ := card_of_lieModel_PSL h
  obtain ⟨h1, h2, h3, h4, h5⟩ := ordA_ne_exceptional (n := m - 1) (by omega)
  rcases card_of_lieModel_exceptional hτ h' with e | e | e | e | e <;> rw [hX] at e
  exacts [h1 e, h2 e, h3 e, h4 e, h5 e]

theorem lieModel_PSp_false_of_exceptional {m n : ℕ} {τ : StatedLieTag}
    (hτ : τ ∈ ({.F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (h : LieModel X .PSp m 2 1) (h' : LieModel X τ n 2 1) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ordBC_ne_exceptional m
  rcases card_of_lieModel_exceptional hτ h' with e | e | e | e | e <;>
    rw [(card_of_lieModel_PSp h).2] at e
  exacts [h1 e, h2 e, h3 e, h4 e, h5 e]

theorem twelve_thousand_lt_card_of_lieModel_exceptional {n : ℕ} {τ : StatedLieTag}
    (hτ : τ ∈ ({.F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))
    (h : LieModel X τ n 2 1) : 12096 < Nat.card X := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := twelve_thousand_lt_exceptional
  rcases card_of_lieModel_exceptional hτ h with e | e | e | e | e <;> rw [e]
  exacts [h1, h2, h3, h4, h5]

end Exceptional

end Ord

end CFSG.LargeExtraspecial.A2Mod
