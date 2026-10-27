module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.LocalOfData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.LocalLeech
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.CoverMonster

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Monster.Existence CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.TwoFi22


theorem localDatum_tGriess_xGriess [Finite MGriess] : LocalDatum MGriess tGriess xGriess := by
  have I : GMSInterfaces (phiB uBar) MGriess := CFSG.YGroups.Y443.gmsInterfaces_MGriess
  have hG : GMSF1Type (phiB uBar) tGriess xGriess := gmsF1Type_MGriess_uncond
  obtain ⟨b, zz, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hxB : IsTwoBCentralizer xGriess := isTwoBCentralizer_MGriess xGriess (IsConj.refl _)
  have htQ : tGriess ∈ leechQ xGriess :=
    h.mem_leechQ_of_isConj_mul (IsConj.refl _) (IsConj.refl _) xGriess_comm_tGriess.symm
      tGriess_mul_xGriess_mem_twoBNbr.1
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness hG.2
  have htL : tGriess ∈ L.typeSet 0 :=
    L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem (IsConj.refl _) htQ (IsConj.refl _))
  have hF : Co2McLFacts := co2McLFacts
  have hA : IsTwoACentralizer tGriess := (CFSG.YGroups.Y443.monster_clauses_MGriess).2.2
  have hKeq : cent2 tGriess (tGriess * xGriess) = centZ tGriess ⊓ centZ xGriess := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have c1 : Commute g tGriess := mem_centralizer_singleton_iff.1 h1
      have c2 : Commute g (tGriess * xGriess) := mem_centralizer_singleton_iff.1 h2
      have c3 : Commute g (tGriess * (tGriess * xGriess)) := c1.mul_right c2
      rw [← mul_assoc, tGriess_mul_self, one_mul] at c3
      exact mem_centralizer_singleton_iff.2 c3
    · rintro ⟨h1, h2⟩
      refine ⟨h1, mem_centralizer_singleton_iff.2 ?_⟩
      exact (show Commute g tGriess from mem_centralizer_singleton_iff.1 h1).mul_right
        (show Commute g xGriess from mem_centralizer_singleton_iff.1 h2)
  have hshape : HasLayeredTwoShape (centZ tGriess ⊓ centZ xGriess) 2 22
      (fun X _ => Nonempty (X ≃* Co2)) := by
    have h1 := twoPointShape_tGriess_mul_xGriess
    unfold TwoPointShape at h1
    rw [hKeq] at h1
    exact h1
  refine ⟨orderOf_tGriess, orderOf_xGriess, ?_, xGriess_comm_tGriess, ?_, ?_, htQ, ?_, ?_, ?_, ?_⟩
  · exact fun hx => not_isConj_xGriess_tGriess (hx ▸ IsConj.refl _)
  · exact RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (Subgroup.equivMapOfInjective (CFSG.pCore 2 ↥(centZ xGriess)) (centZ xGriess).subtype
        (Subgroup.subtype_injective _)) hxB.1
  · exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).trans hxB.2.1
  · obtain ⟨N', hN'n, N₀, hN₀n, hle, hE, hc₀, hQ, hc, ⟨e⟩⟩ := hshape
    exact ⟨N', hN'n, hc.trans (by norm_num), ⟨e⟩⟩
  · have hcent : Nat.card ↥(centZ tGriess) = twoBabyOrder := natCard_cent_tGriess_of hA
    rw [hcent, show twoBabyOrder = 2 ^ 42 * (3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 *
      47) by unfold twoBabyOrder; ring]
    exact factorization_two_pow_mul (by norm_num) (by norm_num)
  · exact fun W htW hzW hWle hinv => L.irreducible_centralizer_inf_one hF htL W htW hzW hWle hinv
  · exact L.mem_commutator_centralizer_inf_one hF htL

theorem monsterLocal : MonsterLocal := by
  have hfin : Finite MGriess := inferInstance
  have hD := localDatum_tGriess_xGriess
  exact ⟨⟨xGriess, hD.mem_centZ⟩, hD.localAt_localR0⟩

end CFSG.EvenSporadicStandard.TwoB
