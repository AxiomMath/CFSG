module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphTowerParab
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphHatDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCosets

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

theorem noTwoSymThree_of_two_bound {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hP : IsParabolicTwo Y P)
    (hb : ∀ P'' : Subgroup A, IsParabolicTwo Y P'' → P'' ≤ P →
      (∀ K : Subgroup A, K ≤ P'' → ⁅K, K⁆ = K → ¬ 3 ∣ Nat.card K) →
      ∀ S : Subgroup A, S ≤ P'' → IsPGroup 2 S → Nat.card S ≤ 2 * Nat.card (pCoreOf 2 P'')) :
    TwelveNotLe.NoTwoSymThree P := by
  obtain ⟨T, S, hT, hTP, hS, hpar, hTU, hsol⟩ := exists_tower hP
  intro X X' hX hX' hXs hXs'
  have hbd : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 (preHatOf P (towerHat S))) :=
    hb _ hpar (preHatOf_le P _) hsol T hTU hT.2.1
  have hTP'' : IsSylowTwoOf T (preHatOf P (towerHat S)) :=
    CFSG.Quasithin.A4.isSylowTwoOf_mono hT hTU ((preHatOf_le P _).trans hP.1)
  have hJT : pCoreOf 2 (preHatOf P (towerHat S)) ≤ T := pCoreOf_le_of_isSylowTwoOf hTP''
  have hJP : pCoreOf 2 (preHatOf P (towerHat S)) ≤ P :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (preHatOf_le P _)
  have hQT : pCoreOf 2 P ≤ T := pCoreOf_le_of_isSylowTwoOf hTP
  have hQJ : pCoreOf 2 P ≤ pCoreOf 2 (preHatOf P (towerHat S)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_preHatOf P _)
      ((preHatOf_le P _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P)
  have hcard : Nat.card (hatOf P T) ≤
      2 * Nat.card (hatOf P (pCoreOf 2 (preHatOf P (towerHat S)))) :=
    card_hatOf_le_two_mul hTP.1 hJP hQT hQJ hbd
  have hKH : hatOf P (pCoreOf 2 (preHatOf P (towerHat S))) ≤ towerHat S := by
    have := hatOf_mono (P := P) (CFSG.LieType.BorelTits.pCoreOf_le 2 (preHatOf P (towerHat S)))
    rwa [hatOf_preHatOf] at this
  have hKn : ((hatOf P (pCoreOf 2 (preHatOf P (towerHat S)))).subgroupOf (towerHat S)).Normal := by
    have := hatOf_normal (P := P) (CFSG.LieType.BorelTits.pCoreOf_le 2 (preHatOf P (towerHat S)))
      (normal_subgroupOf_pCoreOf (preHatOf P (towerHat S)))
    rwa [hatOf_preHatOf] at this
  have hK2 : IsPGroup 2 ↥(hatOf P (pCoreOf 2 (preHatOf P (towerHat S)))) :=
    (CFSG.Quasithin.A4.isPGroup_subgroupOf_of_le hJP
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (preHatOf P (towerHat S)))).map _
  have hKT : hatOf P (pCoreOf 2 (preHatOf P (towerHat S))) ≤
      (S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) := by
    rw [hS]
    exact hatOf_mono hJT
  have hcard' : Nat.card (S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) ≤
      2 * Nat.card (hatOf P (pCoreOf 2 (preHatOf P (towerHat S)))) := by
    rw [hS]
    exact hcard
  exact Sym.eq_of_two_cosets (pCore_two_hat_eq_bot P) hX hX' hXs hXs'
    (le_towerHat_of_subnormal S hX hXs) (le_towerHat_of_subnormal S hX' hXs') hKH hKn hK2 S hKT
    hcard'

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower
