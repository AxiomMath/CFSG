module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3324
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Obs3324

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Obs3324

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem of_c132_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hC32 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hr : IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
    (hcard : Nat.card ↥(autOn L (vPlus L T)) = 360 ∨ Nat.card ↥(autOn L (vPlus L T)) = 6048 ∨
      Nat.card ↥(autOn L (vPlus L T)) = 1080) :
    IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L := by
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hnt := h.not_L_le_centralizer h38 h39
  have hMS := h.isMSPair h38 h39 hr hTL
  rcases hC32 G (L ⊔ T) T L hMS h.toSetup331.mem_cComp
      (Subgroup.coe_mul_of_right_le_normalizer_left L T hTL) with hb | hb | hb | hb | hb
  · exact Or.inr (Or.inr hb)
  · exact Or.inl hb
  · exact (false_of_sp4_or_sl3 hLV (hOQ.trans hQV) hnt h.Lq hcard (Or.inl hb)).elim
  · exact Or.inr (Or.inl hb)
  · exact (false_of_sp4_or_sl3 hLV (hOQ.trans hQV) hnt h.Lq hcard (Or.inr hb)).elim

end Obs3324

theorem obs3_3_24_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h10 : Stmt3_3_10)
    (h14 : Stmt3_3_14_F4) (h16 : Stmt3_3_16_F4) (h19 : Stmt3_3_19_F4) (h21 : Stmt3_3_21_F4)
    (h22 : Stmt3_3_22_F4) (hC32 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4) : Obs3_3_24_F4 := by
  intro G _ _ T M L D h
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hnL2 := (h10 G T M L D h).2.1
  rw [hML] at hnL2
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  obtain ⟨⟨eZ⟩, -⟩ := Obs3324.quot_data hLV (hOQ.trans hQV) (h.not_L_le_centralizer h38 h39) h.Lq
  have hfin : IsRankTwoLie2Derived
      ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) →
      (Nat.card ↥(autOn L (vPlus L T)) = 360 ∨ Nat.card ↥(autOn L (vPlus L T)) = 6048 ∨
        Nat.card ↥(autOn L (vPlus L T)) = 1080) →
      IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
        IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := fun hr hcard => by
    rcases Obs3324.of_c132_F4 h38 h39 hC32 h hTL hr hcard with hb | hb | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hb))
  have hA6 : Nonempty (↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 6)) →
      IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
        IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := fun ⟨e⟩ => by
    have hc0 := SBc11.center_eq_bot_of_list (Or.inr (Or.inl ⟨e⟩))
    exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨eZ.trans ((Obs3324.quotCenterEquiv hc0).trans e)⟩)))))
      (Or.inl (SBc11.card_of_isAlt_six ⟨e⟩))
  obtain ⟨_, hc⟩ := h.lemma_3_3_8_of_le h38 h39 h51 hTL
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    obtain ⟨t, ht, htN, -⟩ := h1
    exact absurd (hTL ht) htN
  ·
    obtain ⟨n, -, hn, -⟩ := h2
    rw [hML] at hn
    exact absurd hn (hnL2 n)
  ·
    rcases h3 with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · rw [hML] at e
      exact absurd (Obs3324.lieModel_of_alt5 e) (hnL2 2)
    · rw [hML] at e
      exact ((h22 G T M L D h).false e).elim
  ·
    rcases h4 with ⟨n, K, _, _, hK, ⟨e⟩, -⟩ | ⟨n, K, _, _, hn, hK, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
      ⟨n, K, _, _, hK, ⟨e⟩, -⟩
    ·
      rw [hML] at e
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · exact Or.inr (Or.inr (Or.inr (Vol2Native.A312L.Seven.isPSL_three_two
            (e.trans (statedSLEquivZModTwo (by rw [hK, pow_one]))))))
      · exact ((h16 G T M L D h n K hn hK).1.false e).elim
    ·
      rw [hML] at e
      exact ((h16 G T M L D h n K hn hK).2.1.false e).elim
    ·
      rw [hML] at e
      exact hA6 ⟨e⟩
    ·
      rw [hML] at e
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
          have hP : IsPSU 3 3 1 ↥(autOn L (vPlus L T)) :=
            Obs3324.isPSU_of_g2Two hK2 e
          have hc0 := SBc11.center_eq_bot_of_list (Or.inr (Or.inr hP))
          exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (Obs3324.isPSU_of_equiv (eZ.trans (Obs3324.quotCenterEquiv hc0)) hP))))))))
            (Or.inr (Or.inl (SBc11.card_of_isPSU_three_three hP)))
      · rw [Obs3324.commutator_quasithinG2_eq hn hK] at e
        exact ((h16 G T M L D h n K hn hK).2.2.false e).elim
  ·
    obtain ⟨⟨e⟩, -⟩ := h5
    rw [hML] at e
    exact ((h22 G T M L D h).false e).elim
  ·
    obtain ⟨-, hZ, ⟨e⟩, -⟩ := h6
    rw [hML] at hZ e
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(autOn L (vPlus L T)))
    rw [Nat.card_congr e.toEquiv, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩, hZ] at hcard
    exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eZ.trans e⟩)))))
      (Or.inr (Or.inr hcard))
  ·
    obtain ⟨n, hn, ⟨e⟩, -⟩ := h7
    rw [hML] at e
    rcases hn with rfl | rfl
    · exact ((h21 G T M L D h).false e).elim
    · exact ((h19 G T M L D h).false e).elim

end CFSG.Quasithin.H13
