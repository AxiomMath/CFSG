module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Reduce
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.OddQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo.Fixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo.Rows

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
open CFSG.ComponentClassification.CatFC

theorem false_of_inner_and_outer_involutions (inp : Thm24ThreeSimpleInputs) (I : ArmInputs)
    {s' : TauCeti.SporadicName} (hs' : s' ∈ Sol78Rows) {H : Type} [Group H] [Finite H]
    {N : Subgroup H} (hN : FStarSimple N) (h2 : N.index = 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {A : Subgroup H} (hA : SolStd A)
    (hcov : OddCover s' A) (hAN : A ≤ N) {a b : H} (ha : a ∈ centralizer (A : Set H))
    (hb : b ∈ centralizer (A : Set H)) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (haN : a ∈ N)
    (hbN : b ∉ N) : False := by
  haveI := hN.isSimpleGroup
  have hna := hN.nonabelian
  have hcat : CFSG.Blueprint.Catalog ↥N :=
    CFSG.EvenSporadicStandard.Induction.Balance.catalog_of_index_two hN h2 hkp
  have hq : CFSG.IsQuasisimple ↥A := hcov.1
  have hcompa := isCompIn_centralizer_of_mem hA hq ha ha2
  have hcompb := isCompIn_centralizer_of_mem hA hq hb hb2
  obtain ⟨σa, Da, hσa, hDa, hina, ⟨ea⟩⟩ :=
    exists_fixedComponent_conjNormal hN ha2 hcompa hAN
  obtain ⟨σb, Db, hσb, hDb, hinb, ⟨eb⟩⟩ :=
    exists_fixedComponent_conjNormal hN hb2 hcompb hAN
  have hσain : σa ∈ (MulAut.conj : ↥N →* MulAut ↥N).range := hina.2 haN
  have hσbout : σb ∉ (MulAut.conj : ↥N →* MulAut ↥N).range := fun h => hbN (hinb.1 h)
  have hs'p : s' ∈ pinnedNames := List.mem_cons_of_mem _ hs'
  have hcard : Nat.card (↥A ⧸ center ↥A) = pinnedOrder s' := by
    haveI : IsSimpleGroup (↥A ⧸ center ↥A) := hq.2.1
    exact inp.card_pinned s' hs'p _ hcov.2.2
  have hca : Nat.card (↥Da ⧸ center ↥Da) = pinnedOrder s' := by
    rw [Nat.card_congr (cqEquivOfMulEquiv ea).toEquiv]
    exact hcard
  have hcb : Nat.card (↥Db ⧸ center ↥Db) = pinnedOrder s' := by
    rw [Nat.card_congr (cqEquivOfMulEquiv eb).toEquiv]
    exact hcard
  obtain ⟨s, ⟨e⟩⟩ :=
    sporadicRep_of_innerFixedComponent I hna hcat hσa hσain hDa hs'p hca
  obtain ⟨hda, hina', -⟩ := I.table hN.isSimpleGroup hna e hσa hDa
  obtain ⟨-, -, houtb⟩ := I.table hN.isSimpleGroup hna e hσb hDb
  rw [hca] at hda hina'
  rw [hcb] at houtb
  exact not_inner_outer_rows hs' hda ⟨hina' hσain, houtb hσbout⟩

end CFSG.EvenSporadicStandard.Induction.Hyp.Thm24ThreeIndexTwo
