module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
public import CFSG.Goldschmidt.Steps.G63Basic
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeU43Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier TauCeti
open CFSG.Open (GriessAllModelsStatement)
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  (SporadicMultipliers card_le_torsion_center lie_center_nine_iso card_center_dvd_twelve
    exists_lieModel center_torsion_le torsBound_le_of_five_le)

theorem centralQuotient_family' {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L)) :
    AltCentralQuotient L ∨ LieCentralQuotient L ∨ SporCentralQuotient L := by
  obtain ⟨i, ⟨φ⟩⟩ := hcat
  have hnab : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := hq.2.2
  cases i with
  | cyclic q hq' =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact Or.inl ⟨n, ⟨φ⟩⟩
  | lie idx => exact Or.inr (Or.inl ⟨idx, ⟨φ⟩⟩)
  | sporadic name => exact Or.inr (Or.inr ⟨name, ⟨φ⟩⟩)

theorem identify_of_two_le_pRank_center' (hGA : GriessAllModelsStatement)
    (hSpM : SporadicMultipliers) {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    p = 3 ∧ Nonempty (L ⧸ Subgroup.center L ≃* X₀) ∧
      Nat.card {z : Subgroup.center L // z ^ 3 = 1} = 9 ∧
      Nat.card (Outer (L ⧸ Subgroup.center L)) = 8 := by
  obtain ⟨E, hEZ, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
  have hp2' : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos h2
  have hEdvd : p ^ 2 ∣ Nat.card (Subgroup.center L) := by
    refine (pow_dvd_pow p h2).trans ?_
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hEZ
  have hcube := hp2'.trans (card_le_torsion_center hEab hEZ)
  have hp3 : 3 ≤ p := hp.two_le.lt_of_ne (Ne.symm hp2)
  have hq' : CFSG.IsQuasisimple L :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      L hq⟩
  rcases centralQuotient_family' hq' hcat with ⟨n, ⟨e⟩⟩ | ⟨d, ⟨e⟩⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    have : Group.IsPerfect L := ⟨hq.1⟩
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
    have hn := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.five_le_of_centerQuotient hq.1 e
    have := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_center_le_one hn e hp hp2
    omega
  · obtain ⟨t, n, p', f, hm⟩ := exists_lieModel d
    have hle := center_torsion_le hGA hq e hm hp
    by_cases hp5 : 5 ≤ p
    · exfalso
      have h1 := hcube.trans (hle.trans (torsBound_le_of_five_le hp5 t n p' f))
      have h2' : p < p ^ 2 := by nlinarith
      omega
    · have hp3' : p = 3 := by
        have := hp.eq_one_or_self_of_dvd 2
        interval_cases p <;> simp_all
      subst hp3'
      obtain ⟨h1, h2', h3⟩ := lie_center_nine_iso hGA hq d e (by omega)
      exact ⟨rfl, h1, le_antisymm h2' (by omega), h3⟩
  · exfalso
    have hd := card_center_dvd_twelve hSpM hq s e
    have h12 : p ^ 2 ∣ 12 := hEdvd.trans hd
    have := Nat.le_of_dvd (by norm_num) h12
    have hp5 : p ≤ 3 := by nlinarith
    obtain rfl : p = 3 := by omega
    omega

theorem center_rank_two' (hGA : GriessAllModelsStatement) (hSpM : SporadicMultipliers)
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h2 : 2 ≤ CFSG.Open.pRank p (Subgroup.center L)) :
    p = 3 ∧ CFSG.Open.pRank 3 (Subgroup.center L) = 2 ∧ 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨rfl, ⟨e⟩, hcube, -⟩ := identify_of_two_le_pRank_center' hGA hSpM hq hcat hp hp2 h2
  obtain ⟨E, hEZ, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center L)
  have hle : Nat.card E ≤ 9 := hcube ▸ card_le_torsion_center hEab hEZ
  have hr : CFSG.Open.pRank 3 (Subgroup.center L) = 2 := by
    refine le_antisymm ?_ h2
    rw [hEcard] at hle
    by_contra hlt
    have : 3 ^ 3 ≤ 3 ^ CFSG.Open.pRank 3 (Subgroup.center L) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨rfl, hr, ?_⟩
  let φ : L →* X₀ := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext g
    simp [φ]
  refine CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.U43Rank.four_le_pRank_of_cover
    φ hφ hker.le (Z := E) (hEZ.trans hker.ge) hEab.2 ?_
  rw [hEcard, hr]
  norm_num

theorem noncyclicCentreRank_of_tables (hGA : GriessAllModelsStatement)
    (hSpM : SporadicMultipliers) : NoncyclicCentreRank := by
  intro L _ _ hq hcat hZ3 hnc
  have h2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.center L) := by
    obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.Goldschmidt.G63.exists_isElemAbelian_card_sq
      Nat.prime_three (by norm_num) hZ3 hnc
    exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hEQ hE hcard
  exact (center_rank_two' hGA hSpM hq hcat Nat.prime_three (by norm_num) h2).2.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
