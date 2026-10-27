module

public import CFSG.Open.GLADefs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem exists_twoLocal_attaining_GLATwoLocalRank {p : ℕ} (hp : p.Prime)
    (hT : ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      ∃ E : Subgroup G, E ≤ Subgroup.normalizer (T : Set G) ∧ IsElemAbelian p E ∧
        Nat.card E = p ^ GLATwoLocalRank p G := by
  have hne : {k | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank p H = k}.Nonempty := by
    obtain ⟨T, hT0, hT2⟩ := hT
    exact ⟨_, ⟨Subgroup.normalizer (T : Set G), ⟨T, hT0, hT2, rfl⟩, rfl⟩⟩
  have hbdd : BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
    have h1 : pRank p H < p ^ pRank p H := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ pRank p H ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
    omega
  obtain ⟨H, hHloc, hHrank⟩ := Nat.sSup_mem hne hbdd
  obtain ⟨T, hT0, hT2, rfl⟩ := hHloc
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
    (Subgroup.normalizer (T : Set G))
  refine ⟨T, hT0, hT2, E, hEH, hE, ?_⟩
  rw [hEc, hHrank]
  rfl

end CFSG.HardMathSupport.Timmesfeld.Proving

end
