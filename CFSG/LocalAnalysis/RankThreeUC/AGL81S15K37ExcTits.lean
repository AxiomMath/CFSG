module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Exc
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Tits3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)

variable {X : Type} [Group X] [Finite X] {K E S : Subgroup X}

section Tits


namespace K37Setting

theorem le_centralizer_tits (h : K37Setting X K E S) (hZ : Subgroup.center ↥K = ⊥)
    {hv : TauCeti.LieTypeIndex.tits.Valid}
    (e : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := ↥K) ⟨hv, ⟨e⟩⟩
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv ↥K 2 1 hmodel
  have hout := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier ↥K 2 1 hmodel).1
  have hin : autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    have hbot := disjoint_self.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _
      ((IsPGroup.of_card h.card_autIm).map
        (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)))
      (hout.to_subgroup _))
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  have hsyl : ∀ P : Sylow 3 ↥K, Nat.card (P : Subgroup ↥K) = 3 ^ 3 := by
    intro P
    have h27 : Nat.card ((P : Subgroup ↥K).map eT.toMonoidHom) = 27 :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.card_sylow_three_titsD
        (P.mapSurjective (f := eT.toMonoidHom) eT.surjective)
    rw [← Subgroup.card_map_of_injective (f := eT.toMonoidHom) eT.injective, h27]
    norm_num
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  have h27 : 3 ^ 3 ∣ Nat.card ↥K := hsyl P ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup ↥K)
  obtain ⟨R, hR, hRΓ⟩ := h.exists_card_eq_le_gamma hZ hin h27
  obtain ⟨Q, hRQ⟩ := (IsPGroup.of_card hR).exists_le_sylow
  have hQR : (Q : Subgroup ↥K) ≤ R :=
    (Subgroup.eq_of_le_of_card_ge hRQ (by rw [hsyl Q, hR])).ge
  exact le_centralizer_of_autIm_eq_bot h.S_le_normalizer_K
    (CFSG.LocalAnalysis.UniquenessCase.UCK.twoSigTriv_tits_three ⟨_, hv⟩ rfl e Q (autIm S K)
      (isPGroup_autIm h.two) fun g hg => h.conj_mem_normalizer_autIm g.2 (hRΓ g (hQR hg)))

theorem le_centralizer_of_exc
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hL28 : CFSG.AGLEmbedding.KFactCaseTwoNoTwoL28)
    (hK35 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.KFactThreeFiveInner)
    (h : K37Setting X K E S) (d : TauCeti.ValidLieTypeIndex)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hexc : (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) ∨ d.1 = .tits) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨e⟩ := hd
  have hZ := h.center_eq_bot hGA d e hexc
  rcases hexc with h28 | ⟨q, hq2, hq1, hdq⟩ | hdq
  · exact h.le_centralizer_l28 hL28 hK35 hZ d h28 ((InputsSeitz3.equivCenterQuot hZ).trans e)
  · obtain ⟨dd, hv⟩ := d
    simp only at hdq
    subst hdq
    exact h.le_centralizer_sp6 hZ hq2 hq1 ((InputsSeitz3.equivCenterQuot hZ).trans e)
  · obtain ⟨dd, hv⟩ := d
    simp only at hdq
    subst hdq
    exact h.le_centralizer_tits hZ ((InputsSeitz3.equivCenterQuot hZ).trans e)

end K37Setting

end Tits

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
