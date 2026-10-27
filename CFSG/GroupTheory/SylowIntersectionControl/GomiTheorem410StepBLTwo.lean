module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.QuasisimpleLTwoCover
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.GroupTheory

private theorem card_bounds_of_valid_A1_bl2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) : 4 ≤ q.card ∧ q.card ≠ 4 := by
  rw [TauCeti.LieTypeIndex.valid_iff] at hv
  have h4 : 4 ≤ q.card := by
    have h := hv.1
    rw [TauCeti.LieTypeIndex.inStandardRange_iff] at h
    exact h.2 rfl
  refine ⟨h4, fun hc => hv.2 ?_⟩
  rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  exact Or.inl ⟨rfl, Or.inl hc⟩

private theorem three_le_exponent_bl2 (k : ℕ) (h4 : 4 ≤ 2 ^ k) (hne : 2 ^ k ≠ 4) : 3 ≤ k := by
  by_contra h
  have hk2 : k ≤ 2 := by omega
  interval_cases k <;> norm_num at *

theorem nonempty_mulEquiv_of_isGomiL2 {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hX2 : CFSG.pCore 2 X = ⊥)
    (h : IsGomiL2 (X ⧸ Subgroup.center X)) :
    Nonempty (X ≃* alternatingGroup (Fin 5)) ∨
      ∃ m : ℕ, 3 ≤ m ∧ Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
  have : Group.IsPerfect X := hX.1
  rw [IsGomiL2] at h
  rcases h with he | ⟨d, hq, he⟩
  · obtain ⟨e⟩ := he
    exact Or.inl (nonempty_mulEquiv_alternatingGroup_five_of_pCore_eq_bot hX2 e)
  · right
    obtain ⟨q, hq2, hd⟩ := hq
    obtain ⟨e⟩ := he
    obtain ⟨d, hv⟩ := d
    dsimp only at hd
    subst hd
    obtain ⟨p, k, hp, hk⟩ := q
    subst hq2
    obtain ⟨h4card, hnecard⟩ := card_bounds_of_valid_A1_bl2 ⟨2, k, hp, hk⟩ hv
    have h4 : 4 ≤ 2 ^ k := by simpa only [TauCeti.PrimePower.card_def] using h4card
    have hne : 2 ^ k ≠ 4 := by simpa only [TauCeti.PrimePower.card_def] using hnecard
    have hk3 : 3 ≤ k := three_le_exponent_bl2 k h4 hne
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have h8 : 8 ≤ Nat.card (GaloisField 2 k) := by
      rw [GaloisField.card 2 k (by omega)]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    refine ⟨k, hk3, ?_⟩
    exact nonempty_mulEquiv_specialLinearGroup_of_isPerfect h8
      (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, k, hp, hk⟩ hv))

end CFSG.GroupTheory
