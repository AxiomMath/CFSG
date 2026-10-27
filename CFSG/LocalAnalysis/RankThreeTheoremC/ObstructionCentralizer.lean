module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentre
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem ExtremalObstruction.centralizer_not_le_of_mem_center (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hD : ¬ IsMulCommutative D) {z : G}
    (hzZ : z ∈ (center D).map D.subtype) (hz1 : z ≠ 1) :
    ¬ centralizer ({z} : Set G) ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, hDM⟩ := hext.obstruction
  have hZc : Nat.card ((center D).map D.subtype) = p := hext.card_center_eq hprime hodd hD
  have hzp : z ^ p = 1 :=
    (hext.pow_eq_one_and_commutator_mem hprime hodd).1 z (map_subtype_le _ hzZ)
  have hZeq : zpowers z = (center D).map D.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzZ) ?_
    rw [hZc, Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hzc : z ∈ centralizer ((P : Subgroup G) : Set G) :=
    hext.center_le_centralizer hprime hodd hD hzZ
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have hND : normalizer (D : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    rw [hZeq]
    exact normalizer_le_normalizer_characteristic_map D (center D) inferInstance
  intro hCM
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) (centralizer ({z} : Set G)) :=
    ⟨P.subtype hPC, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPC]⟩
  have hNz : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M :=
    (le_sup_normalizer_of_isSylowOf (normalizer_zpowers_le_normalizer_centralizer z)
      hPsyl).trans (sup_le hCM (normalizer_sylow_le hS hp hM))
  exact hDM (hND.trans hNz)

end CFSG.LocalAnalysis.RankThreeTheoremC
