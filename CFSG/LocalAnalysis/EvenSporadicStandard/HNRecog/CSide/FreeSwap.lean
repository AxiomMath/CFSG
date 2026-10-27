module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.BaseSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.LinFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Transport

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup Module CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.Fpf
  CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem CSideSetup.cSideFreeSwap_of_four_le [Finite C] (hC : WeakHyp C Q) (S : CSideSetup C Q)
    {t : C} (ht : t ∉ commutator C) (ht2 : (t : C ⧸ Q) ^ 2 = 1)
    (hfree : 4 ≤ finrank (ZMod 2) (LinearMap.range
      ((conjLinEquiv hQn t : Additive (Abelianization Q) →ₗ[ZMod 2] Additive (Abelianization Q))
        + 1))) :
    cSideFreeSwap (extraspecialQuadForm hC.isExtraspecialPGroup) S.σ (conjLinEquiv hQn t) := by
  haveI : Finite Q := hC.finite_Q
  have hQL : Q ≤ commutator C := hC.le_commutator
  have ht2Q : t ^ 2 ∈ Q :=
    (QuotientGroup.eq_one_iff (N := Q) (t ^ 2)).mp (by rwa [QuotientGroup.mk_pow])
  refine ⟨?_, ?_, ?_, hfree⟩
  · have hbb : conjLinEquiv hQn t * conjLinEquiv hQn t = conjLinEquiv hQn (t ^ 2) := by
      rw [← map_mul, ← pow_two]
    rw [hbb, conjLinEquiv_eq_one_of_mem ht2Q]
  · intro v
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (conjLinEquiv_mem hC.isExtraspecialPGroup hQn t) v
  · obtain ⟨s, hs, hb⟩ := S.exists_swap hQL ht ht2
    exact Swap.swapsFactors_of_aut S.σ (conjLinEquiv hQn t) s hs hb

theorem CSideSetup.cSideFreeSwap_of_card_le [Finite C] (hC : WeakHyp C Q) (S : CSideSetup C Q)
    {t : C} (ht : t ∉ commutator C) (ht2 : (t : C ⧸ Q) ^ 2 = 1)
    (hcard : Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} ≤ 2 ^ 5) :
    cSideFreeSwap (extraspecialQuadForm hC.isExtraspecialPGroup) S.σ (conjLinEquiv hQn t) := by
  refine CSideSetup.cSideFreeSwap_of_four_le hC S ht ht2 ?_
  haveI : Finite Q := hC.finite_Q
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  have hcomm := cSide_card_comm_eq hC.isExtraspecialPGroup t
  have h2n : 2 * Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn t v = v} ≤ 32 := by
    rw [← hcomm]
    exact hcard
  have hfix : Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn t v = v} ≤ 16 := by
    omega
  have hV : finrank (ZMod 2) (Additive (Abelianization Q)) = 8 := by
    rw [hC.plus.finrank_quotient]
  exact cSide_four_le_finrank_range hV (conjLinEquiv hQn t) hfix

end CFSG.EvenSporadicStandard.HNRecog.CSide
