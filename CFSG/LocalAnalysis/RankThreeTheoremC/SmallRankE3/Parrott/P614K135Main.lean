module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614R3Defs
import CFSG.LieType.ChevTwo.BorelTitsTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup

namespace P614K135

open CFSG.LieType.BorelTits

theorem eq_pCoreOf_of_radical {X : Type} [Group X] [Finite X] {R P : Subgroup X}
    (hrad : pCoreOf 2 (normalizer (R : Set X)) = R) (hN : normalizer (R : Set X) ≤ P)
    (hRP : R ≤ pCoreOf 2 P) : R = pCoreOf 2 P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hQN : pCoreOf 2 P ⊓ normalizer (R : Set X) ≤ R := by
    refine (le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQp.to_le inf_le_left)).trans hrad.le
    intro g hg
    exact inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 P (hN hg), le_normalizer hg⟩
  by_contra hne
  have hlt : R.subgroupOf (pCoreOf 2 P) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hRP fun y hy => ?_)
    have hy' : (⟨y, hy⟩ : ↥(pCoreOf 2 P)) ∈ R.subgroupOf (pCoreOf 2 P) := htop ▸ mem_top _
    exact mem_subgroupOf.mp hy'
  haveI : Group.IsNilpotent ↥(pCoreOf 2 P) := hQp.isNilpotent
  obtain ⟨n, hnN, hnR⟩ := SetLike.exists_of_lt
    (normalizerCondition_of_isNilpotent (G := ↥(pCoreOf 2 P)) _ hlt)
  rw [← subgroupOf_normalizer_eq hRP, mem_subgroupOf] at hnN
  exact hnR (mem_subgroupOf.mpr (hQN ⟨n.2, hnN⟩))

theorem le_normalizer_of_radical {X : Type} [Group X] [Finite X] {R S P : Subgroup X}
    (hrad : pCoreOf 2 (normalizer (R : Set X)) = R) (hN : normalizer (R : Set X) ≤ P)
    (hRP : R ≤ pCoreOf 2 P) (hSP : S ≤ P) : S ≤ normalizer (R : Set X) := by
  have hR : R = pCoreOf 2 P := eq_pCoreOf_of_radical hrad hN hRP
  have hP : P ≤ normalizer (R : Set X) := by
    rw [hR]
    exact le_normalizer_pCoreOf 2 P
  exact hSP.trans hP

end P614K135

section Certs

theorem kFact135_holds : KFact135 := by
  intro K _ _ hs hna hc R hR hR1 hrad
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, P, -, hN, -, hRP, hSP⟩ :=
    CFSG.LieType.ChevTwo.holdsTits_two_of_isChevTwo hs hna hc R hR1 hR
  exact ⟨S, P614K135.le_normalizer_of_radical hrad hN hRP hSP, S.isPGroup', S.not_dvd_index⟩

theorem kFact135Three_holds : KFact135Three := by
  intro K _ _ hs hna hc _ R hR hR1 hrad
  exact kFact135_holds K hs hna hc R hR hR1 hrad

end Certs

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
