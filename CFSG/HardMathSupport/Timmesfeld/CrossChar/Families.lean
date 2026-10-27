module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterFamilies

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.DefChar

abbrev Cat (idx : TauCeti.ValidLieTypeIndex) : Type := (TauCeti.CFSGIndex.lie idx).Group

@[expose] def CrossCharFam (k : LieFamily) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → idx.1.characteristic ≠ p → IsLocallyBalancedAbs p 3 S

@[expose] def CrossCharFamCat (k : LieFamily) : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
    idx.1.characteristic ≠ p → IsLocallyBalancedAbs p 3 (Cat idx)

theorem CrossCharFam.of_cat {k : LieFamily} (h : CrossCharFamCat k) : CrossCharFam k := by
  intro S _ _ _ _ idx hk ⟨e⟩ p hp hp2 hc
  exact IsLocallyBalancedAbs.of_mulEquiv e (h idx hk p hp hp2 hc)

@[expose] def CrossCharFamAt (k : LieFamily)
    (R : TauCeti.ValidLieTypeIndex → ℕ → Prop) : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
    idx.1.characteristic ≠ p → R idx p → IsLocallyBalancedAbs p 3 (Cat idx)

theorem CrossCharFamAt.mono {k : LieFamily} {R R' : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h : ∀ idx p, R' idx p → R idx p) (hR : CrossCharFamAt k R) : CrossCharFamAt k R' :=
  fun idx hk p hp hp2 hc hr => hR idx hk p hp hp2 hc (h idx p hr)

theorem crossCharFamCat_of_at {k : LieFamily} (R : TauCeti.ValidLieTypeIndex → ℕ → Prop)
    (h₁ : CrossCharFamAt k R) (h₂ : CrossCharFamAt k fun idx p => ¬ R idx p) :
    CrossCharFamCat k := fun idx hk p hp hp2 hc => by
  by_cases hr : R idx p
  · exact h₁ idx hk p hp hp2 hc hr
  · exact h₂ idx hk p hp hp2 hc hr

theorem CrossCharFamAt.of_cat {k : LieFamily} {R : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h : CrossCharFamCat k) : CrossCharFamAt k R :=
  fun idx hk p hp hp2 hc _ => h idx hk p hp hp2 hc

theorem localThreeBalanceCrossChar_of_families (h : ∀ k, CrossCharFam k) :
    LocalThreeBalanceCrossChar := by
  intro S _ _ hS hnab idx hidx p hp hp2 hc
  obtain ⟨k, hk⟩ := exists_lieFamily idx.1
  exact h k S hS hnab idx hk hidx p hp hp2 hc

theorem localThreeBalanceCrossChar_iff_families :
    LocalThreeBalanceCrossChar ↔ ∀ k, CrossCharFam k :=
  ⟨fun h _ S _ _ hS hnab idx _ hidx p hp hp2 hc => h S hS hnab idx hidx p hp hp2 hc,
    localThreeBalanceCrossChar_of_families⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar
