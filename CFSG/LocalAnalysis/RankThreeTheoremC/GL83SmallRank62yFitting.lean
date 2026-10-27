module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yCommon
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr628_fitting_inf_eq_bot (hI : GL83SmallRankInterface G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} {x z : G} {T : Subgroup G} (hf : Prop627Failure G p P M x z T)
    (hcov : SmallRankCover p M x) (h1 : p = 3 ∨ p = 5)
    (h3 : p = 3 → Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2))
    (h5 : p = 5 → smallRankIsQ8D8 (smallRankR x z T)) :
    CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ⊓ M = ⊥ := by
  have hp : p.Prime := hf.prime
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := smallRankD p x with hD
  set O : Subgroup G := rankThreePrimeCore 2 D with hO
  set F : Subgroup G := CFSG.fittingSubgroupOf O with hF
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥(F ⊓ M) ≠ 1 from fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqd
  have hgo : orderOf (g : G) = q := by rw [Subgroup.orderOf_coe]; exact hg
  have hgF : (g : G) ∈ F := g.2.1
  have hgM : (g : G) ∈ M := g.2.2
  have hDspec : D ≤ C ∧ C ≤ normalizer (D : Set G) ∧ Nat.Coprime p (Nat.card D) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p C
  have hOspec : O ≤ D ∧ D ≤ normalizer (O : Set G) ∧ Nat.Coprime 2 (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 D
  have hCO : C ≤ normalizer (O : Set G) := sr628_centralizer_le_normalizer_oddCore p x
  have hOF : normalizer (O : Set G) ≤ normalizer (F : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.fittingSubgroup O)
  have : Group.IsNilpotent F := sr628_isNilpotent_fitting O
  obtain ⟨Q₀, hQ₀p, hQ₀F, hgQ₀, hFQ₀⟩ := sr628_exists_pGroup hgF hgo
  have hCQ₀ : C ≤ normalizer (Q₀ : Set G) := hCO.trans (hOF.trans hFQ₀)
  have hFO : F ≤ O := Subgroup.map_subtype_le _
  have hqO : q ∣ Nat.card O := hgo ▸ Subgroup.orderOf_dvd_natCard O (hFO hgF)
  have hq2 : q ≠ 2 := fun h =>
    absurd (Nat.Coprime.eq_one_of_dvd hOspec.2.2 (h ▸ hqO)) (by norm_num)
  have hqD : q ∣ Nat.card D := hqO.trans (Subgroup.card_dvd_of_le hOspec.1)
  have hqp : q ≠ p := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDspec.2.2 (h ▸ hqD))
  have hQ₀D : Q₀ ≤ D := hQ₀F.trans (hFO.trans hOspec.1)
  have hnormQ₀ : (Q₀.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQ₀D).mpr (hDspec.1.trans hCQ₀)
  have hQ₀Q : Q₀ ≤ pCoreOf q D := CFSG.LieType.BorelTits.le_pCoreOf q hQ₀D hnormQ₀ hQ₀p
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hgo
    exact hq.one_lt.ne hgo
  have hQ₁ne : pCoreOf q D ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : (g : G) ∈ pCoreOf q D ⊓ M := ⟨hQ₀Q hgQ₀, hgM⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hg1 hmem
  have hN₁ : normalizer ((pCoreOf q D ⊓ M : Subgroup G) : Set G) ≤ M :=
    hI.prop65 p P M x z T hf hcov h1 h3 h5 q hq hq2 hqp hQ₁ne
  have hQp : IsPGroup q (pCoreOf q D) := CFSG.LieType.BorelTits.pCoreOf_isPGroup q D
  have hQM : pCoreOf q D ≤ M := by
    by_contra hQM
    have hlt : pCoreOf q D ⊓ M < pCoreOf q D :=
      lt_of_le_of_ne inf_le_left fun heq => hQM (heq.symm.le.trans inf_le_right)
    obtain ⟨y, hyQ, hyN, hyY⟩ := sr628_exists_mem_normalizer_not_mem hQp hlt
    exact hyY ⟨hyQ, hN₁ hyN⟩
  rw [inf_eq_left.mpr hQM] at hN₁
  have hCQ : C ≤ normalizer (pCoreOf q D : Set G) :=
    hDspec.2.1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q D)
  exact hf.point.not_centralizer_le (hCQ.trans hN₁)

end CFSG.LocalAnalysis.RankThreeTheoremC
