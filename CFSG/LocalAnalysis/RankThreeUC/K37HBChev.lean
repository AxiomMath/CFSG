module

public import CFSG.LocalAnalysis.RankThreeUC.K37HBQuot
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ChevStrongD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.Yardstones.Md0ec50421ce4

private theorem card_of_isLTwoTwentySeven' {X : Type} [Group X]
    (h : CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven X) : Nat.card X = 9828 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
  norm_num

private theorem primePower_card_three {q : TauCeti.PrimePower} (h : q.card = 3) : q.p = 3 := by
  rw [TauCeti.PrimePower.card_def] at h
  have hpe : q.p ∣ 3 := by
    rw [← h]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hpe

theorem k37b_rest_of_chevStrong (hC : ChevStrong 3) {X : Type} [Group X] [Finite X]
    {K E S : Subgroup X} (h : K37Setting X K E S) (h3 : 3 ∣ Nat.card K)
    (hchev : IsChevSimple 3 (↥K ⧸ Subgroup.center ↥K))
    (hord : Nat.card (↥K ⧸ Subgroup.center ↥K) ≠ 9828) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨Y, _, _, K', B', ⟨φ⟩, -, hcore, hcomp, hB, hBN, h9, hback⟩ := k37b_quot h h3
  have eZ : (↥K ⧸ Subgroup.center ↥K) ≃* (↥K' ⧸ Subgroup.center ↥K') :=
    QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  refine hback (hC Y K' B' ⟨Nat.prime_three, by norm_num, hcore, hcomp, hB, hBN,
    CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv eZ hchev⟩ ?_)
  rintro ⟨-, ⟨hL27, -⟩ | ⟨-, h3'⟩⟩
  · exact hord ((Nat.card_congr eZ.toEquiv).trans (card_of_isLTwoTwentySeven' hL27))
  · omega

section Holds

set_option linter.unusedSectionVars false


theorem k37Rest₅_holds : K37Rest₅ := by
  intro X _ _ K E S h hO
  obtain ⟨d, ⟨-, h3z, ⟨e⟩⟩, q, hqc, hd⟩ := hO
  have h3 : 3 ∣ Nat.card K := h3z.trans (Subgroup.card_subgroup_dvd_card _)
  refine k37b_rest_of_chevStrong (chevStrong_holds 3) h h3 (Or.inl ⟨.lie d, ?_, ⟨e⟩⟩) ?_
  · show d.1.characteristic = 3
    rw [hd, TauCeti.LieTypeIndex.characteristic_twistedA]
    exact primePower_card_three hqc
  · rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d _ ⟨e⟩, hd]
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, hqc]
    decide +kernel

theorem k37Rest₇_holds : K37Rest₇ := by
  intro X _ _ K E S h hO
  obtain ⟨d, ⟨-, h3z, ⟨e⟩⟩, q, hqc, hd⟩ := hO
  have h3 : 3 ∣ Nat.card K := h3z.trans (Subgroup.card_subgroup_dvd_card _)
  refine k37b_rest_of_chevStrong (chevStrong_holds 3) h h3 (Or.inl ⟨.lie d, ?_, ⟨e⟩⟩) ?_
  · show d.1.characteristic = 3
    rw [hd, TauCeti.LieTypeIndex.characteristic_G2]
    exact primePower_card_three hqc
  · rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d _ ⟨e⟩, hd]
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, hqc]
    decide +kernel

theorem k37Rest₈_holds : K37Rest₈ := by
  intro X _ _ K E S h hO
  obtain ⟨-, h3z, ⟨e⟩⟩ := hO
  have h3 : 3 ∣ Nat.card K := h3z.trans (Subgroup.card_subgroup_dvd_card _)
  have h56 : 5 ≤ 6 := by norm_num
  refine k37b_rest_of_chevStrong (chevStrong_holds 3) h h3
    (Or.inr ⟨.alternating 6 h56, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩), ⟨e⟩⟩) ?_
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

end Holds

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
