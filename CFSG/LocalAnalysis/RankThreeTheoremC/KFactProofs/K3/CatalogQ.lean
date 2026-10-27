module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Parts
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Identify
public import CFSG.LargeExtraspecial.AS35XGen
public import CFSG.Alternating.Multipliers.Small
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open Subgroup
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (SporadicMultipliers
  sporadicMultiplierOrder_dvd_twelve)

theorem exists_prime_five_le_dvd_of_simple {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card S := by
  apply CFSG.LargeExtraspecial.AS35X.exists_prime_five_le_of_not_isSolvable
  intro hsol
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)

@[expose] def K3CatalogQLie : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      3 ∣ Nat.card S → ¬ 9 ∣ Nat.card S →
        ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card S ∧ ¬ q ∣ Nat.card (hopfMultiplier S)

theorem k3CatalogQ_of_lie (hSpM : SporadicMultipliers)
    (hLie : K3CatalogQLie) : K3CatalogQ := by
  intro S _ _ hS hnab ⟨i, ⟨e⟩⟩ h3 h9
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
      obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial h6
      have h720 : Nat.factorial 6 = 720 := by norm_num [Nat.factorial]
      rw [h720] at hm
      apply h9
      rw [hcard]
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
  | lie d => exact hLie d S hS hnab ⟨e⟩ h3 h9

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
