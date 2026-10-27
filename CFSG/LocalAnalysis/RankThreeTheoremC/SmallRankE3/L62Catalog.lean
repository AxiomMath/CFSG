module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62AltRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62LieRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.FiveCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.CatalogQ

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Multiplier
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (SporadicMultipliers
  sporadicMultiplierOrder_dvd_twelve)
open scoped MatrixGroups

@[expose] def K3CatalogQCyc : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup S → 3 ∣ Nat.card S → CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 →
      ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card S ∧ ¬ q ∣ Nat.card (hopfMultiplier S)

@[expose] def K3CatalogQCycLie : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      3 ∣ Nat.card S → CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 →
        ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card S ∧ ¬ q ∣ Nat.card (hopfMultiplier S)

theorem l62_pRank_top_ge_of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T] [Finite T]
    (e : S ≃* T) {n : ℕ} (h : n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T)) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup T) ≤
      CFSG.Open.pRank 3 ((⊤ : Subgroup T).map e.symm.toMonoidHom) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) e.symm.toMonoidHom e.symm.injective ⊤
  have h2 : (⊤ : Subgroup T).map e.symm.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.symm.surjective
  rw [h2] at h1
  exact h.trans h1

theorem k3CatalogQCycLie_of_table (hGA : GriessAllModelsStatement) : K3CatalogQCycLie := by
  intro d S _ _ hS hnab ⟨e⟩ h3 hcyc
  obtain ⟨t, n, p, f, hm⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_lieModel d
  have hM : Nat.card (hopfMultiplier S) =
      CFSG.RankThree.PartTwo.Sec4.Census.tableOrder t n p f := by
    rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv
      e]
    exact (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA hm).2
  by_cases hex : ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card (hopfMultiplier S)
  · exfalso
    obtain ⟨q₀, hq₀, hq₀5, hq₀d⟩ := hex
    rw [hM] at hq₀d
    rcases CFSG.AGLEmbeddingD2.FiveCover.five_le_dvd_tableOrder_cases hq₀ hq₀5 hq₀d with
      ⟨rfl, hq₀n, -⟩ | ⟨rfl, hq₀n, -⟩
    · obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hm
      · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
        have hn2 : 2 ≤ n := hadm.2.2.1
        have hn5 : 5 ≤ n := hq₀5.trans (Nat.le_of_dvd (by omega) hq₀n)
        have h2 := l62_pRank_top_ge_of_mulEquiv (e.trans e')
          (l62_two_le_pRank_statedProj_sl n hn5 K)
        omega
      · have := hadm.2.2.1
        omega
    · obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := hm
      · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hcl
        have hn3 : 3 ≤ n := hadm.2.2.1
        have hn5 : 5 ≤ n := hq₀5.trans (Nat.le_of_dvd (by omega) hq₀n)
        have h2 := l62_pRank_top_ge_of_mulEquiv (e.trans e')
          (l62_two_le_pRank_statedProj_su n hn5 hadm.1 hadm.2.1 K hK)
        omega
      · have := hadm.2.2.1
        omega
  · obtain ⟨q, hq, hq5, hqd⟩ := exists_prime_five_le_dvd_of_simple hS hnab
    exact ⟨q, hq, hq5, hqd, fun hdvd => hex ⟨q, hq, hq5, hdvd⟩⟩

theorem k3CatalogQCyc_of_lie (hSpM : SporadicMultipliers)
    (hLie : K3CatalogQCycLie) : K3CatalogQCyc := by
  intro S _ _ hS hnab ⟨i, ⟨e⟩⟩ h3 hcyc
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn5 =>
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hcard : Nat.card S = Nat.factorial n / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hn : n = 5 := by
      by_contra hne
      have h6 : 6 ≤ n := by omega
      have h2 := l62_pRank_top_ge_of_mulEquiv e (l62_two_le_pRank_alternating n h6)
      omega
    subst hn
    refine ⟨5, by norm_num, le_rfl, ?_, ?_⟩
    · rw [hcard]; decide
    · rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv e,
        (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2]
      norm_num
  | sporadic s =>
    obtain ⟨q, hq, hq5, hqd⟩ := exists_prime_five_le_dvd_of_simple hS hnab
    refine ⟨q, hq, hq5, hqd, ?_⟩
    rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_of_mulEquiv e,
      hSpM.1 s]
    intro hdvd
    have h12 := hdvd.trans (sporadicMultiplierOrder_dvd_twelve s)
    have := Nat.le_of_dvd (by norm_num) h12
    have hq3 : q ≤ 12 := this
    interval_cases q <;> simp_all (config := {decide := true})
  | lie d => exact hLie d S hS hnab ⟨e⟩ h3 hcyc

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
