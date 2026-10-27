module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact131
public import CFSG.LieType.ChevTwo.BorelTitsTwo
public import CFSG.Quasithin.Background.C22PfG
public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Iso
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.Chevalley

namespace C22Pf

theorem holds_two_of_isPSU_three_three
    {X : Type} [Group X] [Finite X] (hX : IsPSU 3 3 1 X) :
    Holds X 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨eA⟩ := SmithC27.nonempty_quasithinG2_mulEquiv_adjointGroup_two hF
  have hH : Holds ↥(quasithinG2 (ZMod 2)) 2 :=
    (holds_adjointGroup_tag .G2 (ZMod 2) 2).of_mulEquiv eA.symm
  have hD : IsPSU 3 3 1 ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ :=
    SmithC27.isPSU_of_equiv_g2Derived hF (MulEquiv.refl _)
  obtain ⟨eD⟩ := SBc17.nonempty_mulEquiv_PSU3_of_isPSU hD
  obtain ⟨eX⟩ := SBc17.nonempty_mulEquiv_PSU3_of_isPSU hX
  have hcardΓ : Nat.card ↥(quasithinG2 (ZMod 2)) = 12096 := by
    rw [SmithC27.card_quasithinG2' (n := 1) (by rw [hF, pow_one]), hF]
    norm_num
  have hcardC : Nat.card (commutator ↥(quasithinG2 (ZMod 2))) = 6048 := by
    rw [← Nat.card_congr (commutatorSubgroupEquiv (quasithinG2 (ZMod 2))).toEquiv]
    exact SBc11.card_of_isPSU_three_three hD
  have hq : IsPGroup 2 (↥(quasithinG2 (ZMod 2)) ⧸ commutator ↥(quasithinG2 (ZMod 2))) := by
    refine IsPGroup.of_card (n := 1) ?_
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (commutator ↥(quasithinG2 (ZMod 2)))
    rw [hcardΓ, hcardC] at h
    rw [pow_one]
    omega
  have hT : HoldsTits (commutator ↥(quasithinG2 (ZMod 2))) 2 :=
    holdsTits_of_normal_of_isPGroup_quotient hq hH
  have hTX : HoldsTits X 2 :=
    hT.of_mulEquiv ((commutatorSubgroupEquiv (quasithinG2 (ZMod 2))).symm.trans
      (eD.trans eX.symm))
  obtain ⟨eU⟩ := u33Pres_mulEquiv_PSU3
  have hNU : Subgroup.normalizer ((u33SylowT : Subgroup U33G) : Set U33G) ≤ u33SylowT := by
    rw [coe_u33SylowT, u33Extra.normalizer_T]
  exact holds_of_holdsTits hTX (normalizer_le_of_mulEquiv (eX.trans eU.symm) u33SylowT hNU)

end C22Pf

end CFSG.Quasithin

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

theorem holds_two_of_isChevSimple_two
    {S : Type} [Group S] [Finite S] (h : IsChevSimple 2 S) : Holds S 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h with ⟨t, n, f, hm⟩ | ⟨e⟩ | h33
  · by_cases ht : t = .Tits
    · subst ht
      exact CFSG.Quasithin.C22Pf.holds_of_holdsTits (holdsTits_of_lieModel_tits hm)
        (CFSG.Quasithin.C22Pf.titsSylowSelfNormalizing_holds S n f hm)
    · exact holds_of_lieModel hm ht
  · obtain ⟨e⟩ := e
    have hA6 : Holds (alternatingGroup (Fin 6)) 2 :=
      CFSG.Quasithin.C22Pf.holds_of_holdsTits CFSG.LieType.ChevTwo.holdsTits_alternating_six
        (fun P => (CFSG.Quasithin.SmithC27.normalizer_eq_of_isSylowTwoOf_alt6
          (CFSG.Quasithin.SmithC27.sylow_two_isSylowTwoOf_top P)).le)
    exact Holds.of_mulEquiv e.symm hA6
  · exact CFSG.Quasithin.C22Pf.holds_two_of_isPSU_three_three h33

theorem kFact131_holds :
    KFact131 :=
  kFact131_of_holds fun _ _ _ h => holds_two_of_isChevSimple_two h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
