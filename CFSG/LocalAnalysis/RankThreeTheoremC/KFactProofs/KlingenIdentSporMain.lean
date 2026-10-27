module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdent
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsTc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoverFiveScal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsM
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporRowsSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms KlingenIdentSporAux


theorem klingenIdentSpor_holds
    : KlingenIdentSpor := by
  intro p _ Y _ _ Rb Y₀ hred hcat hrank K hK huniq hnc hcent hkl s hs ⟨e⟩
  have hp : p.Prime := hred.prime
  have hperf : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hZp := KlingenIdentLieAux.isPGroup_center hred hK
  have hZc := ReducedNongeneration.isCyclic_center_of_unique hred hK huniq
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  haveI : Finite (MulAut K) := MulEquiv.finite_left
  rcases hs with ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, rfl⟩
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .J3) := Finite.of_equiv _ e'.toEquiv
      by_cases hZ : Subgroup.center K = ⊥
      · have eK : K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group :=
          (QuotientGroup.quotientBot.symm.trans
            (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
        exact false_of_J3 hred hK huniq hcent hkl
          (not_dvd_card_outer_of_quotient (not_dvd_card_outer_J3 e' hp (by norm_num))) hZ eK
      · exact ReducedNongeneration.false_of_weakCore_eq_top hred hK huniq
          (weakCore_eq_top_J3_cover hK.2.2 e' hZ hZp hZc)
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .McL) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_McL_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Suz) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Suz_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .ONan) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_ON_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Co1) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Co1_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Co2) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Co2_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Co3) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Co3_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Fi22) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Fi22_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Fi23) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Fi23_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Fi24Prime) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Fi24_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .HN) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_HN_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Ly) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Ly_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Th) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Th_three e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv _ e'.toEquiv
      have hc : 2 < Nat.card (NativeSporadic.Carrier .B) := by
        show 2 < Nat.card NativeSporadic.B
        rw [← Nat.card_congr e'.toEquiv]
        exact two_lt_card_of_nonabelian
          (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2)
      exact false_of_genData hred hK huniq (genData_B_three hc) e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
      have e' := e.trans b.symm
      exact ReducedNongeneration.false_of_weakCore_eq_top hred hK huniq
        (weakCore_eq_top_M_three e' hZp)
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .M22) := Finite.of_equiv _ e'.toEquiv
      exact false_of_rankData hred hK huniq hcent
        (not_dvd_card_outer_of_quotient (not_dvd_card_outer_M22 e' hp (by norm_num))) s2Lemma
        rankData_M22_three e'
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Co1) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Co1_five e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Ly) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_Ly_five e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .HN) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_HN_five e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv _ e'.toEquiv
      exact false_of_genData hred hK huniq genData_B_five_of_scal e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
      exact false_of_genData hred hK huniq (genData_M_five (e.trans b.symm)) (MulEquiv.refl _)
  ·
    rcases hs with rfl | rfl
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
      have e' := e.trans b.symm
      haveI : Finite (NativeSporadic.Carrier .Fi24Prime) := Finite.of_equiv _ e'.toEquiv
      exact false_of_rankData hred hK huniq hcent
        (not_dvd_card_outer_of_quotient (not_dvd_card_outer_Fi24 e' hp (by norm_num))) s2Lemma
        rankData_Fi24_seven e'
    ·
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
      exact false_of_genData hred hK huniq (genData_M_seven (e.trans b.symm)) (MulEquiv.refl _)
  ·
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
    have e' := e.trans b.symm
    exact false_of_rankData hred hK huniq hcent
      (not_dvd_card_outer_of_quotient (not_dvd_card_outer_M e' hp)) s2Lemma
      (rankData_M_thirteen e') (MulEquiv.refl _)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
