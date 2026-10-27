module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.OddQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo.Split
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimpleCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SolStdSubgroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem false_of_commuting_involutions_in (inp : Thm24ThreeSimpleInputs)
    {s' : TauCeti.SporadicName} (hs' : s' ∈ Sol78Rows) {H : Type} [Group H] [Finite H]
    {N : Subgroup H} (hN : FStarSimple N)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {A : Subgroup H} (hA : SolStd A)
    (hcov : OddCover s' A) (hAN : A ≤ N) {x y : H} (hxN : x ∈ N) (hyN : y ∈ N)
    (hx : x ∈ centralizer (A : Set H)) (hy : y ∈ centralizer (A : Set H)) (hx2 : orderOf x = 2)
    (hy2 : orderOf y = 2) (hxy : x ≠ y) (hcomm : x * y = y * x) : False := by
  haveI := hN.isSimpleGroup
  have hAsub : SolStd (A.subgroupOf N) := solStd_subgroupOf hAN hxN hx2 hx hA
  have hcov' : OddCover s' (A.subgroupOf N) :=
    oddCover_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAN).symm hcov
  have hkpN : CFSG.Assembly.KProper CFSG.Blueprint.Catalog ↥N :=
    kProper_of_section hkp N (MonoidHom.id ↥N) Function.surjective_id
  exact thm24Three_simple_of_inputs inp hs' ↥N hN.nonabelian hkpN (A.subgroupOf N) hAsub hcov'
    (two_le_pRank_centralizer_subgroupOf hxN hyN hx hy hx2 hy2 hxy hcomm)

end CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo
