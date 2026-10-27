module

import CFSG.CGT.Foote82.BlocksCommute
public import CFSG.CGT.Foote82.EF1Bridge

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem core_le_centralizerModTwoCore {M L : Subgroup G} (hL : IsFooteBlock M L) :
    pCoreOf 2 M ≤ centralizerModTwoCore L := fun h hh =>
  mem_centralizerModTwoCore_of_isFooteBlock hL hL.le hh
    (Subgroup.le_normalizer (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hh))

theorem d1_chiefHyp (hG : IsCharTwoType G) {M N L : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hN : GLBIsMaxTwoLocal N) (hL : IsFooteBlock M L) (hLF : IsFType L) (hLN : L ≤ N)
    (hQN : pCoreOf 2 M ≤ N) (hPQ : pCoreOf 2 N ≤ pCoreOf 2 M) :
    ChiefHyp N L (pCoreOf 2 M) := by
  have hK : IsFooteBlock L L := IsFooteBlock.self hL
  have hfaith : N ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ pCoreOf 2 N := hG N hN.1
  have hQC := core_le_centralizerModTwoCore hL
  have hQL : pCoreOf 2 M ≤ Subgroup.normalizer (L : Set G) := fun q hq =>
    (mem_centralizerModTwoCore_iff.mp (hQC hq)).1
  have hcQ : ⁅pCoreOf 2 M, L⁆ ≤ blockQ L :=
    (Subgroup.commutator_le).mpr fun q hq l hl => by
      rw [commutatorElement_def]
      exact (mem_centralizerModTwoCore_iff.mp (hQC hq)).2 l hl
  have hMQ : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hQ0 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨R, hR0, hR2, hMR⟩ := hM.1
    intro hbot
    apply hR0
    have hRM : R ≤ M := hMR ▸ Subgroup.le_normalizer
    have hRQ : R ≤ pCoreOf 2 M :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 R M hRM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr (hMR ▸ le_rfl)) hR2
    rw [hbot] at hRQ
    exact le_bot_iff.mp hRQ
  have hNQM : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    hM.2 _ ⟨pCoreOf 2 M, hQ0, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M, rfl⟩ hMQ
  have hsubM : IsSubnormal L (N ⊓ Subgroup.normalizer (pCoreOf 2 M : Set G)) := by
    rw [hNQM]
    have := CFSG.Open.IsSubnormal.inf_of_le hL.subnormal (inf_le_right : N ⊓ M ≤ M)
    rwa [inf_eq_left.mpr (le_inf hLN hL.le)] at this
  exact
    { faithful := hfaith
      block := hK
      ftype := hLF
      two := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
      core_le := hPQ
      le := hQN
      normalizes := hQL
      cent := hcQ
      blockU_le := blockU_le_core hK hLN hfaith (hPQ.trans hQL)
        ((Subgroup.commutator_mono hPQ le_rfl).trans hcQ)
      subnormal := hsubM }

theorem block_le_of_normalizer_le {M N J L : Subgroup G} (hJ : IsFooteBlock M J)
    (hL : IsFooteBlock M L) (hJN : Subgroup.normalizer (J : Set G) ≤ N) : L ≤ N := by
  by_cases hLJ : L = J
  · exact hLJ ▸ Subgroup.le_normalizer.trans hJN
  · have hc := blocks_commute hL hJ hLJ
    refine le_trans ?_ hJN
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : l * x = x * l :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hl x hx |>.symm
      rw [this, mul_inv_cancel_right]
      exact hx
    · intro hx
      have hlx : l * x * l⁻¹ ∈ J := hx
      have hcomm : ∀ y ∈ J, l * y = y * l := fun y hy =>
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hl y hy).symm
      have : x = l⁻¹ * (l * x * l⁻¹) * l := by group
      rw [this]
      have h1 : l⁻¹ * (l * x * l⁻¹) = (l * x * l⁻¹) * l⁻¹ := by
        have := hcomm _ hlx
        calc l⁻¹ * (l * x * l⁻¹) = l⁻¹ * ((l * x * l⁻¹) * l) * l⁻¹ := by group
          _ = l⁻¹ * (l * (l * x * l⁻¹)) * l⁻¹ := by rw [this]
          _ = (l * x * l⁻¹) * l⁻¹ := by group
      rw [h1, mul_assoc, inv_mul_cancel, mul_one]
      exact hlx

theorem core_le_of_normalizer_le {M N J : Subgroup G} (hJ : IsFooteBlock M J)
    (hJN : Subgroup.normalizer (J : Set G) ≤ N) : pCoreOf 2 M ≤ N := fun q hq =>
  hJN (mem_centralizerModTwoCore_iff.mp (core_le_centralizerModTwoCore hJ hq)).1

end CFSG.CGT.Foote82
