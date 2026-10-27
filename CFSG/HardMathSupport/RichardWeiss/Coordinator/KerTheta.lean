module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KerThetaTwoCore
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent blockV barM)
open CFSG.Open (pCoreOf)
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (SectionEquiv theta_eq_one_iff
  inf_centralizer_blockV_le_pCoreOf card_center_barM_sup_eq_one)

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem inf_centralizer_blockV_eq_pCoreOf (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m)) :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) = pCoreOf 2 (L ⊔ S) := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_center_barM_sup_eq_one hA' hLs hSL hm e)
  refine le_antisymm (inf_centralizer_blockV_le_pCoreOf hA' hLs hSL
    (CFSG.HardMathSupport.Cooperstein.Coordinator.not_le_centralizer_blockV hA hL hSL) hZ) ?_
  exact le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (L ⊔ S))
    (fun x hx => CFSG.AGLEmbedding.AscTenThree.le_centralizer_omegaOneCenterOf_self _ hx)

end CFSG.HardMathSupport.RichardWeiss.Coordinator
