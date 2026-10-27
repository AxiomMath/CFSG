module

public import CFSG.GH74.NoComponent
public import CFSG.GH74.QTGen4.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.QTKEAssemblyUnique
public import CFSG.Quasithin.H13.AssemblyTheoremD
public import CFSG.Quasithin.H13.LocDblSporadic
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Quasithin.H13.Assembly
public import CFSG.Quasithin.H13.AssemblyVocab
public import CFSG.Quasithin.Recognition.Kleidman.F204.O2Rep
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.GH74.QTGen4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

theorem sevenModels_of_GH (h137 : Stmt13_1_7_GH) (h1312 : Stmt13_1_2_three_GH)
    (h13316 : Stmt13_3_16_GH) (h1361 : Stmt13_6_1_GH) (h1381 : Stmt13_8_1_GH)
    (h14813 : Stmt14_8_1_three_GH) {G : Type} [Group G] [Finite G] (hc : GHCtx G)
    {T L : Subgroup G} (hH : QTH13 G T L) (hmax : quasithinIsMaximalLocal T L) :
    SevenModels G := by
  have hq := h137 G hc T hH.simple hH.nonabelian hH.qtke hH.sylow hH.not_excluded L hH.faithful
  rcases h1312 G hc T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.not_excluded hmax hH.faithful
      hq with hA5 | hL32 | hA6 | ⟨-, -, hA6c⟩ | hU33
  · rcases h1361 G hc T L hH ((quasithinO2QuotientIso_iff L _).2 hA5) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases h14813 G hc T L hH hL32 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · rcases h1381 G hc T L hH (nonempty_quotient_center_equiv_of_equiv_alt6 hA6) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases h1381 G hc T L hH hA6c with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact absurd hU33 (h13316 G hc T L hH)

theorem catalog_of_faithful_nonempty_GH
    (h137 : Stmt13_1_7_GH) (h1312 : Stmt13_1_2_three_GH)
    (h13316 : Stmt13_3_16_GH) (h1361 : Stmt13_6_1_GH) (h1381 : Stmt13_8_1_GH)
    (h14813 : Stmt14_8_1_three_GH) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hc : GHCtx G) (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : quasithinIsQTKECat G)
    (T : Sylow 2 G)
    (hLf : ∃ L : Subgroup G, CFSG.Open.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    Catalog G := by
  have hT : quasithinIsSylowTwo (T : Subgroup G) := ⟨T.isPGroup', T.not_dvd_index⟩
  have hD := H13.LocDbl.local_double_embedding_exclusion
  rcases excluded_or_preferred_local hD inferInstance hnonab hqtke hT
      (faithful_maximal_local_nonempty hD inferInstance hnonab hqtke hT hLf) with h | ⟨L, hL, hH⟩
  · exact h
  · exact catalog_of_sevenModels (sevenModels_of_GH h137 h1312 h13316 h1361 h1381 h14813 hc hH hL.1)

theorem catalog_of_faithful_empty_GH
    (h14 : Stmt15_3_1_GH)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hc : GHCtx G)
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G) (T : Sylow 2 G)
    (hMT : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₁ ∧
      CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal M₂ ∧
      (T : Subgroup G) ≤ M₁ ∧ (T : Subgroup G) ≤ M₂)
    (hLf : ∀ L : Subgroup G,
      ¬ CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L) :
    CFSG.Blueprint.Catalog G := by
  classical
  have h15 : EmptyFaithfulMultiple.MultipleCentralizerRecognitionStatement :=
    EmptyFaithfulMultiple.multipleCentralizerRecognition_of_inputs asB56_holds
      F6.GoldAmLarge.goldschmidtCharTwoLarge_holds
  have hTne := EmptyFaithfulMultiple.sylow_ne_bot hnonab T
  have hsyl : quasithinIsSylowTwo (T : Subgroup G) := ⟨T.isPGroup', T.not_dvd_index⟩
  have hLf' : ∀ L : Subgroup G, ¬ CFSG.Open.quasithinIsFaithfulLocal (T : Subgroup G) L := fun L h =>
    hLf L (EmptyFaithfulMultiple.quasithinIsFaithfulLocal_assembly_iff_open.mpr h)
  set Z := quasithinOmegaOneCenter (T : Subgroup G) with hZ
  have hCN : Subgroup.centralizer (Z : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨Mc, hMc, hNMc⟩ := exists_maxTwoLocal_ge
    (EmptyFaithfulMultiple.isTwoLocal_normalizer_omegaOneCenter T.isPGroup' hTne)
  have hCMc := hCN.trans hNMc
  have hTC : (T : Subgroup G) ≤ Subgroup.centralizer (Z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ (T : Subgroup G) ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) := by
      have : Z ≤ (T : Subgroup G) ⊓ Subgroup.centralizer ((T : Subgroup G) : Set G) :=
        (Subgroup.closure_le _).mpr fun w hw => hw.1
      exact this hz
    exact (Subgroup.mem_centralizer_iff.mp hz'.2 x hx).symm
  by_cases huniq : ∀ M : Subgroup G, quasithinIsMaxTwoLocal M →
      Subgroup.centralizer (Z : Set G) ≤ M → M = Mc
  ·
    apply EmptyFaithfulMultiple.catalog_of_theoremE_alternatives_native
      EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds
    left
    refine h14 G hc (T : Subgroup G) Mc ⟨‹_›, hnonab, hqtke, hsyl, hLf', hMc, hTC.trans hCMc, hCMc,
      huniq, ?_⟩
    obtain ⟨M₁, M₂, hne, hM₁, hM₂, hTM₁, hTM₂⟩ := hMT
    by_cases h₁ : M₁ = Mc
    · exact ⟨M₂, hM₂, hTM₂, fun h => hne (h₁.trans h.symm)⟩
    · exact ⟨M₁, hM₁, hTM₁, h₁⟩
  ·
    push Not at huniq
    obtain ⟨M, hM, hCM, hMne⟩ := huniq
    apply EmptyFaithfulMultiple.catalog_of_theoremE_alternatives_native
      EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds
    right
    exact h15 G (T : Subgroup G) ⟨‹_›, hnonab, hqtke, hsyl, hLf',
      ⟨M, Mc, hMne, hM, hMc, hCM, hCMc⟩⟩

theorem s_QTKE_Gen4_of_inputs
    (h137 : Stmt13_1_7_GH) (h1312 : Stmt13_1_2_three_GH)
    (h13316 : Stmt13_3_16_GH) (h1361 : Stmt13_6_1_GH) (h1381 : Stmt13_8_1_GH)
    (h14813 : Stmt14_8_1_three_GH) (h1531 : Stmt15_3_1_GH) : S_QTKE_Gen4 := by
  intro G _ _ hs hnonab hrank hgen hK hev he
  have hc : GHCtx G := ⟨hgen, hrank, hK⟩
  have hqtke : quasithinIsQTKECat G := ⟨kProper_of_kgh hK, hev, he⟩
  obtain ⟨heven, -⟩ := ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 G))
  obtain ⟨M, hM, hTM⟩ :=
    exists_maxTwoLocal_ge_sylow T (T.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven))
  by_cases huniq : ∃! M : Subgroup G, quasithinIsMaxTwoLocal M ∧ (T : Subgroup G) ≤ M
  · exact uniqueMaximalLocalCat_proved G hnonab hqtke T huniq
  by_cases hLf : ∃ L : Subgroup G, CFSG.Assembly.Quasithin.quasithinIsFaithfulLocal (T : Subgroup G) L
  · exact catalog_of_faithful_nonempty_GH h137 h1312 h13316 h1361 h1381 h14813 G hc hnonab hqtke T
      (hLf.imp fun _ h => quasithinIsFaithfulLocal_open_iff.mpr h)
  · exact catalog_of_faithful_empty_GH h1531 G hc hnonab hqtke T
      (two_maxTwoLocal_of_not_unique hM hTM huniq) fun L hL => hLf ⟨L, hL⟩

end CFSG.GH74.QTGen4
