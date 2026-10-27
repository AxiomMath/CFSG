module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.TimmesfeldDvd47
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Leech

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.EvenSporadicStandard.TwoFi22 CFSG.LargeExtraspecial.Bridge

theorem gmsLeechCentralizer_of_timmesfeld_dvd47 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hT : Timmesfeld78Co1Dvd47) (h47 : 47 ∣ Nat.card G) {L : Subgroup G} {t z : G}
    (hc : CentralPair G L t z) (h54 : IsTwoConstrained (centZ z)) (h55 : Conclusion55 G L t z)
    (h57 : Psub z ≤ Rsub z t) : CFSG.Monster.GMS.GMSLeechCentralizer z := by
  have hz : orderOf z = 2 := (Subgroup.orderOf_mk z hc.hz).symm.trans hc.loc.order_z
  have hP : Rsub z t = Psub z := le_antisymm h55.le_P h57
  let eP : ↥(CFSG.pCore 2 ↥(centZ z)) ≃* ↥(Psub z) :=
    Subgroup.equivMapOfInjective _ (centZ z).subtype (centZ z).subtype_injective
  let e : ↥(Rsub z t) ≃* ↥(CFSG.pCore 2 ↥(centZ z)) := (MulEquiv.subgroupCongr hP).trans eP.symm
  have hext : CFSG.IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥(centZ z)) :=
    RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv e h55.extraspecial
  have hcard : Nat.card (CFSG.pCore 2 ↥(centZ z)) = 2 ^ 25 :=
    (Nat.card_congr e.toEquiv).symm.trans h55.card
  have hcen : centralizer ((CFSG.pCore 2 ↥(centZ z) : Subgroup ↥(centZ z)) :
      Set ↥(centZ z)) ≤ CFSG.pCore 2 ↥(centZ z) := by
    intro c hc'
    have hcG : (c : G) ∈ centralizer ((Psub z : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 hc' q hq)
    have h1 : (c : G) ∈ centZ z ⊓ centralizer ((O2In (centZ z) : Subgroup G) : Set G) :=
      ⟨c.2, hcG⟩
    obtain ⟨q, hq, hqc⟩ := h54 h1
    have : c = q := Subtype.ext hqc.symm
    rw [this]
    exact hq
  obtain ⟨f⟩ := hT G z h47 hz hext hcard hcen (exists_co2_le_quotient hc h55)
  exact gmsLeechCentralizer_of_shape hz hext hcard hcen f

end CFSG.EvenSporadicStandard.TwoB
