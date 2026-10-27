module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeCent
public import Certificates.Certificate13505

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd.S2 CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartOne.StrongP CFSG.RankThree.PartOne CFSG.HardMathSupport.Timmesfeld.Tables.Census

section Centralizer


theorem ruThree_oPrime :
    3 ^ 3 ∣ Nat.card ↥(Subgroup.centralizer ({ruThreeX0} : Set ↥ruP)) ∧
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({ruThreeX0} : Set ↥ruP)) = ⊥ := by
  have hclass : gfr3ClassOK 4060 ruThreeC0Cert.pts 2160 4 1 = true :=
    Certificates.certificate13505
  have henum := CFSG.RankThree.PartOne.centOKP_enum ruThree_case0_check.2.2.2.2.1
  obtain ⟨hC0eq, hC0card⟩ := ruThreeC0_spec
  have hcl : Nat.card ruThreeC0 = 3 ^ 3 * (2 ^ 4 * 5 ^ 1) := by
    rw [hC0card]
    norm_num
  have hcs : ∀ w ∈ ruThreeC0, (orderOf w = 2 → Nat.card ↥(ruThreeC0 ⊓ Subgroup.centralizer
        ({w} : Set (Equiv.Perm (Fin 4060)))) * 2 ^ 4 < 2160) ∧
      (orderOf w = 5 → Nat.card ↥(ruThreeC0 ⊓ Subgroup.centralizer
        ({w} : Set (Equiv.Perm (Fin 4060)))) * (2 ^ 4 * 5 ^ 1) < 2160) := fun w hw =>
    gfr3_classOK_spec ruThreeKeys_lt henum hclass hw
  have hO : GLAPPrimeCoreOf 3 ruThreeC0 = ⊥ :=
    gfr3_oPrime_bot_of_class (a := 3) (e := 4) (f := 1) hcl
      (fun w hw ho => by rw [hC0card]; exact (hcs w hw).1 ho)
      (fun w hw ho => by rw [hC0card]; exact (hcs w hw).2 ho)
  obtain ⟨hcardC, hOs⟩ := gfr3_oPrime_subtype ruP ruThreeX0 ruThreeC0 hC0eq hO
  refine ⟨?_, hOs⟩
  rw [hcardC, hC0card]
  norm_num

end Centralizer

theorem gfr3_noncomm_of_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : HasNoncommPair 3 G) : HasNoncommPair 3 G' :=
  HasNoncommPair.map e.toMonoidHom e.injective h

theorem balance_Ru_three :
    IsLocallyBalancedAbs 3 2 CFSG.Blueprint.NativeSporadic.Ru := by
  refine IsLocallyBalancedAbs.of_mulEquiv ruEquivP ?_
  have hall : ∀ α : MulAut ruP, α ∈ innerAut ruP := fun α => by
    obtain ⟨g, hg⟩ := conj_bijective.2 α
    exact ⟨g, hg⟩
  obtain ⟨h27, hOs⟩ := ruThree_oPrime
  have hnc : HasNoncommPair 3 ↥ruP := gfr3_noncomm_of_equiv (G := CFSG.Blueprint.NativeSporadic.Ru) (G' := ↥ruP) ruEquivP
    pair_Ru_three
  have h81 : ¬ 3 ^ 4 ∣ Nat.card ↥ruP := by
    rw [card_ruP_three]
    norm_num
  exact gfr3_locallyBalanced_of_good center_ruP (gfr3_card_outer_le_two_of_inner hall)
    (gfr3_exists_good_of_sylow hnc h81 orderOf_ruThreeX0 h27 (gfr3_good_of_inner hall hOs))

end CFSG.HardMathSupport.Solomon.Coordinator
