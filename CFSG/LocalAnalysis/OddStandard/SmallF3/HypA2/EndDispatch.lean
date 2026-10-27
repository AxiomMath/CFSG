module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndAlt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndEven
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndR1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SLTwoDatum

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem false_of_inSA (hAlt : CFSG.OddStandard.AltStdCyclicBalancedFalse)
    (hEven : EvenResidualStd) (hCTSS : CTSSStd) (hP : Phase2Inputs) (hL : Leaves2)
    (hI : Phase1Inputs) (hA7 : TwoA7RankOne) {G : Type} [Group G] [Finite G] {x : G}
    {Y : Subgroup G} (hY : EndData G x Y) (hA : InSA (↥Y ⧸ center ↥Y))
    (S : Sylow 2 ↥(Subgroup.centralizer (Y : Set G)))
    (hS : IsCyclic ↥(S : Subgroup ↥(Subgroup.centralizer (Y : Set G)))) : False := by
  haveI := hY.setting.simple
  by_cases halt : ∃ n : ℕ, 5 ≤ n ∧ Nonempty (↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin n))
  · rcases halt with ⟨n, hn5, ⟨e⟩⟩
    have hn8 : 8 ≤ n := by
      by_contra hn
      have hnlt : n < 8 := not_le.mp hn
      have hcard : Nat.card (↥Y ⧸ center ↥Y) = Nat.card (alternatingGroup (Fin n)) :=
        Nat.card_congr e.toEquiv
      have hle : 20160 ≤ Nat.card (alternatingGroup (Fin n)) := by
        rw [← hcard]
        exact hA.2.1
      interval_cases n <;> rw [nat_card_alternatingGroup, Nat.card_fin] at hle <;> norm_num at hle
    exact false_of_alternating hAlt hL.twoAnSL25 hI hA7 hY hn8 ⟨e⟩ S hS
  · exact false_of_even_cyclic hEven hCTSS hP.smallLie hP.g2Derived hY hA halt S hS

theorem false_of_inSB (hL2 : CFSG.Yardstones.M0362f3a873a3.OddLieThm187bResidualL2Ree)
    (hL : Leaves2) (hI : Phase1Inputs) (hA7 : TwoA7RankOne) {G : Type} [Group G] [Finite G]
    {x : G} {Y : Subgroup G} (hY : EndData G x Y) (hB : InSB (↥Y ⧸ center ↥Y))
    (S : Sylow 2 ↥(Subgroup.centralizer (Y : Set G)))
    (hS : IsCyclic ↥(S : Subgroup ↥(Subgroup.centralizer (Y : Set G)))) : False := by
  haveI := hY.setting.simple
  by_cases hpsl : ∃ e : ℕ, LieModel (↥Y ⧸ center ↥Y) .PSL 2 3 e
  · rcases hpsl with ⟨e, he⟩
    have hpow : ∃ j : ℕ, e = 2 ^ j := hB.2.2.2.1 e he
    have h8 : 8 ≤ e := eight_le_of_lieModel_psl_two_three he hB.2.1
    by_cases hZ : center ↥Y = ⊥
    · exact false_of_psl_two_three hL2 hY hZ he hB.2.1 hpow S hS
    · have h9 : 9 ≤ 3 ^ e := by
        have h2 : 2 ≤ e := by omega
        calc (9 : ℕ) = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ e := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 3) h2
      have hdat : CentralDatum ↥Y :=
        centralDatum_of_psl_two hI.griess hY.isQuasisimple hY.isPGroup_center hZ
          Nat.prime_three (by norm_num) h9 he
      exact false_of_centralDatum hI hA7 G hY.setting.nonab hY.setting.kProper
        hY.setting.notCat x Y hY.ox hY.comp hdat
  · have hdat : KDatum ↥Y :=
      hL.chev3End ↥Y hY.isQuasisimple hY.isPGroup_center hB hpsl
    exact false_of_kDatum hI hA7 G hY.setting.nonab hY.setting.kProper hY.setting.notCat
      hY.setting.balanced x Y hY.ox hY.comp hdat

end CFSG.OddStandard.SmallF3.HypA2
