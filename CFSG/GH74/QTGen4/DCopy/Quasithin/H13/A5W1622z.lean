module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1620Tb
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622s
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622u
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622y

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem lemma13622C_of_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4)
    (h132fsu : Stmt13_3_2_three_fsu_F4) (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : Stmt13_2_7_F4) (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4)
    (h124 : ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G))
    (hF318 : A318Facts) (hKF : KnownFacts15122Types) (hres : Lem13622Case4Z0_F4)
    (hRed : Lemma13620L32Red_F4) (hA7 : Lem13622A7Block_F4) : Lemma13622C_F4 := by
  intro G _ _ T L V S hH K hK hYz hT
  have hF := hH.hF
  have hz := S.not_le_centralizer_z_of_inYz hYz hT
  have hchar : CharTwo (K ⊔ S.Tv) :=
    C1GN.charTwo_of_le hF (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right (sup_le hYz.1 S.Tv_le_Gv)

  have hqs : ∀ N : ℕ, (N = 360 ∨ N = 2520 ∨ N = 6048) →
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = N →
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro N hN hc
    rcases S.kbar_cases_F4 h1222 h517 hF h36 h37 h38 hK hYz hT
        (by rw [hc]; rcases hN with rfl | rfl | rfl <;> simp) with h | ⟨h168, -⟩
    · exact h
    · exfalso
      rw [hc] at h168
      rcases hN with rfl | rfl | rfl <;> norm_num at h168

  have hms : S.Lv ≤ K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      (IsPSL 3 2 1 (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) ∨
        IsAlt 6 (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) ∨
        IsPSU 3 3 1 (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K))) → False := by
    intro hLvK hq hlist
    obtain ⟨hRk, h64⟩ := S.msPair_data_of_plus_F4 h1222 h517 hF h37 h38 hK hYz hT hq hlist
    exact S.false_of_msPair_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 h132 h134 hres
      hH ⟨hYz.1, hYz.2.1, hT, hz, hLvK, hchar⟩ hRk h64
  refine ⟨fun F _ _ hF2 ⟨e⟩ => ?_, fun h6 => ?_, fun F _ _ hF2 ⟨e⟩ => ?_, fun hh => ?_,
    fun h7 => ?_⟩
  ·
    exact S.false_of_L32_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h36 h37 h38 h39 h132 h134
      hres hRed hH hK hYz hT hF2 e
  ·
    have hcard : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 360 := by
      rw [Nat.card_congr (quotCenterEquivOfEqBot
        (SBc11.center_eq_bot_of_list (Or.inr (Or.inl h6)))).toEquiv]
      exact SBc11.card_of_isAlt_six h6
    have hq := hqs 360 (Or.inl rfl) hcard
    have hLvK := S.Lv_le_of_rankTwo_F4 h1222 h517 hF318 h36 h37 h38 hKF hF hK hYz hT hq (Or.inl h6)
    exact hms hLvK hq (S.plus_list (Or.inr (Or.inl h6)))
  ·
    have h2 : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        Nonempty (↥(S.plus K) ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆) :=
      ⟨F, inferInstance, inferInstance, hF2, ⟨e⟩⟩
    have hU := SBd8.trioIsPSU33 h2
    have hcard : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 6048 := by
      rw [Nat.card_congr (quotCenterEquivOfEqBot
        (SBc11.center_eq_bot_of_list (Or.inr (Or.inr hU)))).toEquiv]
      exact SBc11.card_of_isPSU_three_three hU
    have hq := hqs 6048 (Or.inr (Or.inr rfl)) hcard
    have hLvK := S.Lv_le_of_rankTwo_F4 h1222 h517 hF318 h36 h37 h38 hKF hF hK hYz hT hq
      (Or.inr (Or.inl h2))
    exact hms hLvK hq (S.plus_list (Or.inr (Or.inr (Or.inl h2))))
  ·
    have hcard : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 360 := by
      obtain ⟨-, -, ⟨e6⟩⟩ := hh
      exact SBc11.card_of_isAlt_six ⟨e6⟩
    have hq := hqs 360 (Or.inl rfl) hcard
    have hLvK := S.Lv_le_of_rankTwo_F4 h1222 h517 hF318 h36 h37 h38 hKF hF hK hYz hT hq
      (Or.inr (Or.inr (Or.inl hh)))
    exact hms hLvK hq (S.plus_list (Or.inr (Or.inr (Or.inr hh))))
  ·
    obtain ⟨e7⟩ := id h7
    have hs7 : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have hsP : IsSimpleGroup ↥(S.plus K) := e7.isSimpleGroup
    have hZ : Subgroup.center ↥(S.plus K) = ⊥ :=
      center_eq_bot_of_isSimple_of_isQuasisimple hsP (S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT)
    have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.factorial]
    have hcard : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 2520 := by
      rw [Nat.card_congr ((quotCenterEquivOfEqBot hZ).trans e7).toEquiv, h2520]
    have hq := hqs 2520 (Or.inr (Or.inl rfl)) hcard
    have hLvK := S.Lv_le_of_rankTwo_F4 h1222 h517 hF318 h36 h37 h38 hKF hF hK hYz hT hq
      (Or.inr (Or.inr (Or.inr h7)))
    exact S.false_of_c124_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h38 h39 h132 h134 hres
      (h124 G) hA7 hH hK hYz hT hLvK hq h7

end CFSG.Quasithin.H13.A5
