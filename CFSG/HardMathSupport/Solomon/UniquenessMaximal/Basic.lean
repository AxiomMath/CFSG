module

public import CFSG.LocalAnalysis.GLTheoremB.BaseCase
public import CFSG.LocalAnalysis.GLTheoremB.Statements

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

@[expose] def IsPreUniquenessSubgroup (p : ℕ) (B M₀ : Subgroup G) : Prop :=
  lambdaStarGroup p B ≤ M₀ ∧ GLBCore p 3 B ≤ M₀ ∧ Even (Nat.card (GLAPPrimeCoreOf p M₀))

theorem IsPreUniquenessTwoLocal.isPreUniquenessSubgroup (hp : p.Prime) (hp2 : p ≠ 2)
    {B M : Subgroup G} (h : IsPreUniquenessTwoLocal p B M) : IsPreUniquenessSubgroup p B M :=
  ⟨h.2.1, h.2.2, even_card_glaPPrimeCoreOf_of_isTwoLocal hp hp2 h.1.1⟩

theorem IsPreUniquenessSubgroup.isPreUniquenessTwoLocal {B M : Subgroup G}
    (h : IsPreUniquenessSubgroup p B M) (hM : GLAIsMaxTwoLocal M) :
    IsPreUniquenessTwoLocal p B M :=
  ⟨hM, h.1, h.2.1⟩

section Consequences

variable (hS : GLStanding G m p) {B M₀ : Subgroup G} (hB : IsBOneMax p B)
  (hM : IsPreUniquenessSubgroup p B M₀)
include hS hB hM

theorem IsPreUniquenessSubgroup.le : B ≤ M₀ := by
  have h3 : 3 ≤ pRank p B := by
    have := CFSG.SectionRank.le_pRank hS.prime.one_lt le_rfl hB.1.1 (hS.card_eq hB)
    have := hS.four_le
    omega
  exact Subgroup.le_normalizer.trans
    ((le_sSup ⟨B, le_rfl, h3, rfl⟩ : Subgroup.normalizer (B : Set G) ≤ GLBCore p 3 B).trans
      hM.2.1)

theorem IsPreUniquenessSubgroup.normalizer_le_of_hyperplane {K : Subgroup G} (hKB : K ≤ B)
    (hidx : (K.subgroupOf B).index = p) : Subgroup.normalizer (K : Set G) ≤ M₀ := by
  have hp := hS.prime
  have hm4 := hS.four_le
  have hB' : Nat.card B = p ^ ((m - 1) + 1) := by
    rw [Nat.sub_add_cancel (by omega)]
    exact hS.card_eq hB
  have hKcard := card_eq_of_index_eq hp hKB hidx hB'
  have hKel : IsElemAbelian p K := isElemAbelian_mono hB.1.1 hKB
  have h3 : 3 ≤ pRank p K := by
    have := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hKel hKcard
    omega
  exact (le_sSup ⟨K, hKB, h3, rfl⟩ : Subgroup.normalizer (K : Set G) ≤ GLBCore p 3 B).trans hM.2.1

theorem IsPreUniquenessSubgroup.le_of_normalized {Y : Subgroup G}
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hY : ¬ p ∣ Nat.card Y) : Y ≤ M₀ := by
  have : Fact p.Prime := ⟨hS.prime⟩
  have := hS.nontrivial hB
  refine (le_iSup_inf_centralizer_hyperplane hB.1.1 hBY hY).trans (iSup₂_le fun K hK => ?_)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    (hM.normalizer_le_of_hyperplane hS hB hK.1 hK.2))

theorem IsPreUniquenessSubgroup.pCoreOf_two_le {N : Subgroup G} (hBN : B ≤ N) :
    pCoreOf 2 N ≤ M₀ := by
  have hp2 := hS.ne_two
  refine hM.le_of_normalized hS hB
    (hBN.trans ((le_normalizer_pCoreOf 2 N))) ?_
  intro hdvd
  have hP := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk] at hdvd
  have := (Nat.Prime.dvd_of_dvd_pow hS.prime hdvd)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hS.prime Nat.prime_two).1 this)

end Consequences

@[expose] def ExistsPreUniquenessSubgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∃ B : Subgroup G, IsBOneMax p B ∧ ∃ M₀ : Subgroup G, IsPreUniquenessSubgroup p B M₀

@[expose] def Prop81Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B M₀ : Subgroup G, IsBOneMax p B → IsPreUniquenessSubgroup p B M₀ → pCoreOf 2 M₀ ≠ ⊥

theorem exists_isMaxTwoLocal_of_pCoreOf_ne_bot {M₀ : Subgroup G} (h : pCoreOf 2 M₀ ≠ ⊥) :
    ∃ M : Subgroup G, GLAIsMaxTwoLocal M ∧ M₀ ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M₀ : Set G)) :=
    ⟨pCoreOf 2 M₀, h, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀, rfl⟩
  have hle : M₀ ≤ Subgroup.normalizer (pCoreOf 2 M₀ : Set G) := le_normalizer_pCoreOf 2 M₀
  classical
  let S : Set (Subgroup G) := {H | IsTwoLocal H ∧ M₀ ≤ H}
  have hSne : S.Nonempty := ⟨_, hloc, hle⟩
  obtain ⟨M, hMS, hMmax⟩ := (Set.toFinite S).exists_maximalFor id S hSne
  refine ⟨M, ⟨hMS.1, fun H hH hMH => ?_⟩, hMS.2⟩
  exact (le_antisymm (hMmax ⟨hH, hMS.2.trans hMH⟩ hMH) hMH)

theorem theoremOne_of_prop81Core (hex : ExistsPreUniquenessSubgroup) (h81 : Prop81Core) :
    TheoremOne := by
  intro G _ _ _ hna hK hC he m hm hweak p hp hrank hΔ
  have hS : GLStanding G m p :=
    ⟨‹_›, hna, hK, hC, he, hm, hweak, hp, hrank, hΔ⟩
  obtain ⟨B, hB, M₀, hM₀⟩ := hex G m p hS
  obtain ⟨M, hM, hM₀M⟩ := exists_isMaxTwoLocal_of_pCoreOf_ne_bot (h81 G m p hS B M₀ hB hM₀)
  exact ⟨B, hB, M, hM, hM₀.1.trans hM₀M, hM₀.2.1.trans hM₀M⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
