module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.LitX
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24OneOrder

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem cyclic_sylow_of_lit (lit : Sol78LitCore) (lx : OddLieCompNotSporadic) {H : Type} [Group H]
    [Finite H] {N : Subgroup H} (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {A : Subgroup H} (hA : SolStd A)
    {s' : TauCeti.SporadicName} (hs' : s' ∈ Sol78Rows) (hcov : OddCover s' A) :
    ∃ P : Sylow 2 (centralizer (A : Set H)), IsCyclic ↥P := by
  have := hN.normal
  have hAN : A ≤ N := le_of_perfect_of_index_le_two hidx hcov.1.1
  have hord : ¬ Nat.card ↥N ∣ 95040 :=
    not_card_dvd_95040_of_cover lit.thm24_3Simple (List.mem_cons_of_mem _ hs') hAN hcov.1 hcov.2.2
  refine cyclic_sylow_of_std lit.thm24_1 hN hord hA hcov ?_ (oddLieExcl_of_lit lx s')
  by_contra h
  exact lit.thm24_3 s' hs' H N hN hidx hkp A hA hcov (by omega)

end CFSG.EvenSporadicStandard.Induction.Hyp
