module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G] [Finite G]

theorem pRank_le_glaTwoLocalRank_of_isTwoLocal {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hH : IsTwoLocal H) : CFSG.Open.pRank p H ≤ GLATwoLocalRank p G :=
  le_csSup ⟨CFSG.Open.pRank p (⊤ : Subgroup G), by
    rintro j ⟨H, -, rfl⟩
    exact CFSG.SectionRank.pRank_mono hp.one_lt le_top⟩ ⟨_, hH, rfl⟩

theorem glaTwoLocalRank_subgroup_le {p : ℕ} (hp : p.Prime) (X : Subgroup G) :
    GLATwoLocalRank p ↥X ≤ GLATwoLocalRank p G := by
  refine csSup_le' fun k hk => ?_
  obtain ⟨H, ⟨T, hT, hT2, rfl⟩, rfl⟩ := hk
  have hTmap : T.map X.subtype ≠ ⊥ := by
    intro h
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T X.subtype_injective).1 h)
  have hloc : IsTwoLocal (Subgroup.normalizer ((T.map X.subtype : Subgroup G) : Set G)) :=
    ⟨_, hTmap, hT2.map _, rfl⟩
  calc CFSG.Open.pRank p (Subgroup.normalizer (T : Set ↥X))
      = CFSG.Open.pRank p ((Subgroup.normalizer (T : Set ↥X)).map X.subtype) :=
        (pRank_map_eq_of_injective hp.one_lt X.subtype X.subtype_injective _).symm
    _ ≤ CFSG.Open.pRank p (Subgroup.normalizer ((T.map X.subtype : Subgroup G) : Set G)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt (Subgroup.le_normalizer_map _)
    _ ≤ GLATwoLocalRank p G := pRank_le_glaTwoLocalRank_of_isTwoLocal hp hloc

theorem pRank_le_glaTwoLocalRank_of_normalizes {p : ℕ} (hp : p.Prime) {E T : Subgroup G}
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    CFSG.Open.pRank p E ≤ GLATwoLocalRank p G :=
  (CFSG.SectionRank.pRank_mono hp.one_lt hET).trans
    (pRank_le_glaTwoLocalRank_of_isTwoLocal hp ⟨T, hT, hT2, rfl⟩)

theorem exists_twoGroup_normalized_of_coprime_even {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    {E Y : Subgroup G} (hE : IsPGroup p E) (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    (hcop : ¬ p ∣ Nat.card Y) (heven : Even (Nat.card Y)) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ T ≤ Y ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTY, hT2, hTc, hET⟩ := exists_sylow_normalized_of_not_dvd (q := 2) Y E hE hEY hcop
  refine ⟨T, ?_, hTY, hT2, hET⟩
  intro h
  have h1 := hTc 1 (by simpa using even_iff_two_dvd.1 heven)
  rw [h, Subgroup.card_bot] at h1
  simp at h1

end CFSG.HardMathSupport.Solomon.LocalBalance
