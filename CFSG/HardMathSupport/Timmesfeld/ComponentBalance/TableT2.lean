module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeU43Rank

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open (GriessAllModelsStatement)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  (identify_of_two_le_pRank_center card_le_torsion_center SporadicMultipliers)
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer centerQuotientOuterHom
  centerQuotient_outer_injective)

theorem center_rank_two (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    p = 3 ∧ Nonempty (L ⧸ Subgroup.center L ≃* X₀) ∧
      Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Assembly.RankThreeEven.projSU 4 3 1) ∧
      CFSG.Open.pRank 3 (Subgroup.center L) = 2 ∧
      Nat.card (Outer (L ⧸ Subgroup.center L)) = 8 ∧
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨rfl, ⟨e⟩, hcube, hout⟩ := identify_of_two_le_pRank_center hGA hSpM hq hK hp hp2 h2
  obtain ⟨E, hEZ, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
  have hle : Nat.card E ≤ 9 := hcube ▸ card_le_torsion_center hEab hEZ
  have hr : CFSG.Open.pRank 3 (Subgroup.center L) = 2 := by
    refine le_antisymm ?_ h2
    rw [hEcard] at hle
    by_contra hlt
    have : 3 ^ 3 ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.center L) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨rfl, ⟨e⟩, ?_, hr, hout, ?_⟩
  · obtain ⟨eX⟩ := CFSG.LieType.Multipliers.U43.nonempty_mulEquiv_X₀
      CFSG.RankThree.PartTwo.Sec4.Census.NineCoverU43.lieModel_U43
    exact ⟨e.trans eX.symm⟩
  · let φ : L →* X₀ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : φ.ker = Subgroup.center L := by
      ext g
      simp [φ]
    refine CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.U43Rank.four_le_pRank_of_cover
      φ hφ hker.le (Z := E) (hEZ.trans hker.ge) hEab.2 ?_
    rw [hEcard, hr]
    norm_num

theorem table112_T2_of_tables (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers) :
    ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → CFSG.Open.IsKGroup L →
      ∀ p : ℕ, p.Prime → p ≠ 2 →
        2 * CFSG.Open.pRank p (Subgroup.center L) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
  intro L _ _ hq hK p hp hp2
  rcases Nat.lt_or_ge (CFSG.Open.pRank p (Subgroup.center L)) 2 with hlt | hge
  · rcases Nat.lt_or_ge (CFSG.Open.pRank p (Subgroup.center L)) 1 with h0 | h1
    · omega
    · have hr : CFSG.Open.pRank p (Subgroup.center L) = 1 := by omega
      obtain ⟨E, hEZ, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
      have hpZ : p ∣ Nat.card (Subgroup.center L) := by
        rw [hr, pow_one] at hEcard
        exact hEcard ▸ Subgroup.card_dvd_of_le hEZ
      have : Fact p.Prime := ⟨hp⟩
      have : Group.IsPerfect L := ⟨hq.1⟩
      have hpL : p ∣ Nat.card L := hpZ.trans (Subgroup.card_subgroup_dvd_card _)
      have h := (CFSG.SectionRank.perfect_cyclic_center_odd_elements hp2 hpL).2 hpZ
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
      omega
  · obtain ⟨rfl, -, -, hr, -, h4⟩ := center_rank_two hGA hSpM hq hK hp hp2 hge
    omega

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
