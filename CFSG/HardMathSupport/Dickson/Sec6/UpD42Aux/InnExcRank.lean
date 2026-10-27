module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Chev2Split
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Rank
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamSz
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVKit
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem exists_elemAbelian_81_of_isD42 {G : Type} [Group G] (h : IsCatalogLieIso G IsD42Index) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ :=
    CFSG.GH74.statedClassicalModel_of_lieModel (by decide) (lieModel_of_isD42 h)
  obtain ⟨e'⟩ := CFSG.LocalAnalysis.GLTheoremA.D4XF.equiv_projOmegaPlus_of_statedProj
    (by rw [hK₀]; norm_num) e
  obtain ⟨D, hD, hDc⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.exists_e81_of_three_lt_pRank
      CFSG.RankThree.PartTwo.Sec4.Census.three_lt_pRank_omegaPlus
  refine ⟨D.map e'.symm.toMonoidHom, isElemAbelian_map_up34 _ e'.symm.injective hD, ?_⟩
  rw [Subgroup.card_map_of_injective e'.symm.injective, hDc]

theorem UpD42Pumpup.exists_elemAbelian_81_fixed {S : Type} [Group S] [Finite S] {α : MulAut S}
    (h : UpD42Pumpup S α) :
    ∃ E : Subgroup ↥(fixSubgroup α), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, I, hI, hD⟩ := h
  obtain ⟨Eb, hEb, hEb81⟩ := exists_elemAbelian_81_of_isD42 hD
  have hN3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥I) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_gLAPPrimeCore_aux 3 ↥I)
  obtain ⟨P, -, hP, hPcard⟩ := CFSG.RankThree.Classical2.exists_elemAbelian_lift (p := 3)
    (GLAPPrimeCore 3 ↥I) hN3 hEb
  have hinj := Subgroup.inclusion_injective hI.1
  refine ⟨P.map (Subgroup.inclusion hI.1),
    isElemAbelian_map_up34 _ hinj hP, ?_⟩
  rw [Subgroup.card_map_of_injective hinj, hPcard, hEb81]

theorem UpD42Pumpup.exists_elemAbelian_81 {S : Type} [Group S] [Finite S] {α : MulAut S}
    (h : UpD42Pumpup S α) :
    ∃ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  obtain ⟨E, hE, hc⟩ := h.exists_elemAbelian_81_fixed
  refine ⟨E.map (fixSubgroup α).subtype,
    isElemAbelian_map_up34 _ (Subgroup.subtype_injective _) hE, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hc]

theorem UpD42Pumpup.card_dvd {S : Type} [Group S] [Finite S] {α : MulAut S}
    (h : UpD42Pumpup S α) : 174182400 ∣ Nat.card S := by
  obtain ⟨-, -, I, -, hD⟩ := h
  rw [← card_of_isD42Type hD]
  exact (Subgroup.card_quotient_dvd_card (GLAPPrimeCore 3 ↥I)).trans
    (Subgroup.card_subgroup_dvd_card I)

theorem upD42Chev2Inn_of_rank {F : TauCeti.LieTypeIndex → Prop}
    (hrank : ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), F d.1 →
      IsCharTwoLieIndex d.1 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → RankLE2 3 S) :
    UpD42Chev2Inn F := by
  intro S _ _ hs hnab d hd hc he x hx
  obtain ⟨E, hE, hcard⟩ := hx.exists_elemAbelian_81
  have h9 := hrank S d hd hc he E hE
  rw [hcard] at h9
  norm_num at h9


theorem upD42Chev2Inn_g2 : UpD42Chev2Inn FamG2 := by
  refine upD42Chev2Inn_of_rank fun S _ _ ⟨d, hv⟩ hF hc ⟨e⟩ => ?_
  cases d with
  | G2 q =>
    have h3 : 3 ≠ q.p := by
      have : q.p = 2 := hc
      omega
    exact RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv h3)
  | _ => exact hF.elim

theorem upD42Chev2Inn_triD4 : UpD42Chev2Inn FamTriD4 := by
  refine upD42Chev2Inn_of_rank fun S _ _ ⟨d, hv⟩ hF hc ⟨e⟩ => ?_
  cases d with
  | trialityD4 q =>
    have h3 : q.p ≠ 3 := by
      have : q.p = 2 := hc
      omega
    exact RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv h3)
  | _ => exact hF.elim

theorem upD42Chev2Inn_reeF4 : UpD42Chev2Inn FamReeF4 := by
  refine upD42Chev2Inn_of_rank fun S _ _ ⟨d, hv⟩ hF hc ⟨e⟩ => ?_
  cases d with
  | reeF4 m =>
    exact RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv)
  | _ => exact hF.elim

theorem upD42Chev2Inn_sz : UpD42Chev2Inn FamSz := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | suzuki m =>
    have hadm : StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) :=
      ⟨Nat.prime_two, by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
        omega, rfl, rfl, odd_two_mul_add_one m, by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
        omega⟩
    have hm := blueprintLieModel_suzuki m hv e
    obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
      .twistedB2 0 2 (2 * m + 1) hadm hm
    have h3 : 3 ∣ Nat.card S := (by norm_num : 3 ∣ 174182400).trans hx.card_dvd
    have h3' : 3 ∣ lieOrderNumerator .twistedB2 0 (2 ^ (2 * m + 1)) := by
      rw [← hord]
      exact Dvd.dvd.mul_right h3 _
    exact absurd h3' (I923.not_three_dvd_suzuki_numerator (odd_two_mul_add_one m))
  | _ => exact hF.elim

theorem upD42Chev2Inn_tits : UpD42Chev2Inn FamTits := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hx
  cases d with
  | tits =>
    have hadm : StatedLieAdmissible .Tits 0 2 1 := ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩
    have hm := blueprintLieModel_tits hv e
    obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
      .Tits 0 2 1 hadm hm
    have h7 : 7 ∣ Nat.card S := (by norm_num : 7 ∣ 174182400).trans hx.card_dvd
    have : Nat.card S = 17971200 := by
      simpa [lieOrderDivisor, lieOrderNumerator] using hord
    rw [this] at h7
    exact absurd h7 (by norm_num)
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
