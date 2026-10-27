module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCasesProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenParabolicOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 Subgroup

@[expose] def KFactTransvectionW3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P : Subgroup A), P ≤ Y → Open.pRank 3 Y ≤ 3 →
    ((∃ (m : ℕ) (d d' : TauCeti.ValidLieTypeIndex),
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ (d.1 = .D m q ∨ d.1 = .twistedD m q)) ∧
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B (m - 1) q) ∧
        Nonempty (↥Y ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
        Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* (TauCeti.CFSGIndex.lie d').Group)) ∨
      (((∃ d : TauCeti.ValidLieTypeIndex,
          (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q) ∧
          Nonempty (↥Y ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        Nonempty (↥Y ≃* alternatingGroup (Fin 8))) ∧ Nonempty (↥P ≃* Equiv.Perm (Fin 6))) ∨
      (Nonempty (↥Y ≃* alternatingGroup (Fin 5)) ∧ Nonempty (↥P ≃* Equiv.Perm (Fin 3)))) →
    ∀ b : A, Odd (orderOf b) → b ∈ normalizer (Y : Set A) → b ∈ normalizer (P : Set A) →
      (∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
          wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) →
      ∀ y ∈ Y, b * y = y * b

variable {G : Type} [Group G] [Finite G]

theorem pRank_three_barM_le_of {M : Subgroup G} (hM : Open.pRank 3 M ≤ 3) (L : Subgroup G) :
    Open.pRank 3 (barM M L) ≤ 3 := by
  have hLM : barM M L ≤ barM M M := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have h1 : Open.pRank 3 (barM M L) ≤ Open.pRank 3 (barM M M) :=
    CFSG.SectionRank.pRank_mono (by norm_num) hLM
  have h2 := stmtBarPRankLift Nat.prime_three (by norm_num) M M le_rfl
  omega

theorem pRank_three_le (hS : Setting G) {M : Subgroup G} (hM : IsTwoLocal M) :
    Open.pRank 3 M ≤ 3 := by
  have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) M hM
  rw [hS.rank] at h
  exact h

theorem pRank_three_barM_le (hS : Setting G) {M : Subgroup G} (hM : IsTwoLocal M)
    (L : Subgroup G) : Open.pRank 3 (barM M L) ≤ 3 :=
  pRank_three_barM_le_of (pRank_three_le hS hM) L

theorem tenThreeThreeAt_three3 (hKF : KFactTransvectionW3) :
    TenThreeThreeAt G (fun M S L => NineThreeThree M S L ∧ ¬ InClassXBlock L ∧
      ¬ CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L ∧ Open.pRank 3 M ≤ 3) := by
  intro M H L hK hA hNH hMS hL hLn ⟨h3, hX, hS, hM3⟩ b hb hbo hbJ
  have hrk := pRank_three_barM_le_of hM3 L
  have hLM : L ≤ M := hL.le
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds G M
      (pCoreOf 2 H) L hK hA hL hX hS h3
  have hPP : barM M (H ⊓ L) = blockPL M (pCoreOf 2 H) L := by rw [blockPL, hNS]
  set eP := MulEquiv.subgroupCongr hPP
  have tr : ∀ {T : Type} [Group T], Nonempty (↥(blockPL M (pCoreOf 2 H) L) ≃* T) →
      Nonempty (↥(barM M (H ⊓ L)) ≃* T) := fun ⟨e⟩ => ⟨eP.trans e⟩
  have trq : ∀ {T : Type} [Group T], Nonempty (↥(blockPL M (pCoreOf 2 H) L) ⧸
      CFSG.pCore 2 ↥(blockPL M (pCoreOf 2 H) L) ≃* T) →
      Nonempty (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃* T) := by
    rintro T _ ⟨e⟩
    obtain ⟨e'⟩ := nonempty_quotient_pCore_mulEquiv eP
    exact ⟨e'.trans e⟩
  obtain ⟨hbbo, hbLbar, hbP, hW⟩ := bar_action hLM hLn hb hbo hbJ
  have hPY : barM M (H ⊓ L) ≤ barM M L := map_mono fun x hx => by
    rw [mem_subgroupOf] at hx ⊢
    exact hx.2
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', hd', hP⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      exact Or.inr (commutator_mem_pCoreOf_of_centralizes hLM hb.2
        (hKF _ _ _ hPY hrk (Or.inl ⟨m, d, d', ⟨q, hq, Or.inl hd⟩, hd', ⟨e⟩, trq hP⟩) _ hbbo hbLbar hbP hW))
    · obtain ⟨d', hd', hP⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      exact Or.inr (commutator_mem_pCoreOf_of_centralizes hLM hb.2
        (hKF _ _ _ hPY hrk (Or.inl ⟨m, d, d', ⟨q, hq, Or.inr hd⟩, hd', ⟨e⟩, trq hP⟩) _ hbbo hbLbar hbP hW))
    · exact Or.inr (commutator_mem_pCoreOf_of_centralizes hLM hb.2
        (hKF _ _ _ hPY hrk (Or.inr (Or.inl ⟨Or.inl ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩, tr (hU4 d ⟨q, hq, hd⟩ ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (commutator_mem_pCoreOf_of_centralizes hLM hb.2
        (hKF _ _ _ hPY hrk (Or.inr (Or.inr ⟨⟨e⟩, tr (hA5 ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
    · left
      obtain ⟨e4⟩ := tr (hA6 ⟨e⟩)
      obtain ⟨h1, h2⟩ := altSix_sFour_odd hPY e e4
      have hk : L ⊓ pCoreOf 2 M ≤ H := fun x hx =>
        (CFSG.LieType.BorelTits.pCoreOf_le 2 H) (hMS hx.2)
      exact not_two_dvd_relIndex_jZero hLM hk h1 h2
    · exact Or.inr (commutator_mem_pCoreOf_of_centralizes hLM hb.2
        (hKF _ _ _ hPY hrk (Or.inr (Or.inl ⟨Or.inr ⟨e⟩, tr (hA8 ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))

variable (G) in
structure TenThreeThreeLeavesNX3 : Prop where
  three : TenThreeThreeAt G (fun M S L => NineThreeThree M S L ∧ ¬ InClassXBlock L ∧
    ¬ CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ L) L ∧ Open.pRank 3 M ≤ 3)
  four : TenThreeThreeAt G (fun M S L => NineThreeFour M S L)
  six : TenThreeThreeAt G (fun M S L => NineThreeSix M S L ∧ ¬ InClassXBlock L)
  seven : TenThreeThreeAt G (fun M S L => NineThreeSeven M S L ∧ ¬ InClassXBlock L)
  eight : TenThreeThreeAt G (fun M S L => NineThreeEight M S L ∧ ¬ InClassXBlock L)

theorem tenThreeThreeLeavesNX3_of (hKT : KFactTransvectionW3) (hAlt : Asc81bAltBlockAutNX) :
    TenThreeThreeLeavesNX3 G :=
  ⟨tenThreeThreeAt_three3 hKT, tenThreeThreeAt_four G,
    tenThreeThreeAt_alt_nx hAlt fun _ _ _ h => ⟨Or.inl h.1, h.2⟩,
    tenThreeThreeAt_alt_nx hAlt fun _ _ _ h => ⟨Or.inr (Or.inl h.1), h.2⟩,
    tenThreeThreeAt_alt_nx hAlt fun _ _ _ h => ⟨Or.inr (Or.inr h.1), h.2⟩⟩

theorem tenThreeThreeAt_core_nx3 (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : NoXBlockFor G) (hKF : KFactParabolicW) (hlv : TenThreeThreeLeavesNX3 G)
    (hS : Setting G) {M H : Subgroup G} (hT : TwoLocalPhaseThree M H)
    (hMS : pCoreOf 2 M ≤ pCoreOf 2 H) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hLn : (L.subgroupOf M).Normal) (hA7 : IsEmpty (↥(barM M L) ≃* alternatingGroup (Fin 7)))
    {b : G} (hb : b ∈ H ⊓ M) (hbo : Odd (orderOf b))
    (hbJ : ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) :
    ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L ∨
      ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hLX : ¬ InClassXBlock L := (hT.nineThree_not_one hK h85 hNX hL).1
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 (hT.nineThree_not_one hK h85 hNX hL).1
  · exact tenThreeThreeAt_of_parabolic hKF M H L hK hA hNH hMS hL hLn h2 b hb hbo hbJ
  · exact hlv.three M H L hK hA hNH hMS hL hLn
      ⟨h3, (hT.nineThree_not_one hK h85 hNX hL).1, hT.not_isSylowTwoOf_inf hK h85 hNX hL,
        pRank_three_le hS hT.maxTwoLocal_M.1⟩ b
      hb hbo hbJ
  · exact hlv.four M H L hK hA hNH hMS hL hLn h4 b hb hbo hbJ
  · exact (hA7.false h5.2.1.some).elim
  · exact hlv.six M H L hK hA hNH hMS hL hLn ⟨h6, hLX⟩ b hb hbo hbJ
  · exact hlv.seven M H L hK hA hNH hMS hL hLn ⟨h7, hLX⟩ b hb hbo hbJ
  · exact hlv.eight M H L hK hA hNH hMS hL hLn ⟨h8, hLX⟩ b hb hbo hbJ

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem agl81TenThreeThreeCfg_holds_nx3 (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) (hKP : TenThreeThree.KFactParabolicW)
    (hKT : TenThreeThree.KFactTransvectionW3) (hAlt : TenThreeThree.Asc81bAltBlockAutNX)
    (hA7 : AGL81TenNineOneCfg G) : AGL81TenThreeThreeCfg G := by
  intro hS p P M H Q K hd L hL hLn B hBHM hB hBJ
  refine TenThreeThree.concl_of_forall fun b hb => ?_
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  exact TenThreeThree.tenThreeThreeAt_core_nx3 h85 h93 hNX hKP
    (TenThreeThree.tenThreeThreeLeavesNX3_of hKT hAlt) hS (hd.toTwoLocalPhaseThree' hS h98)
    (hd.nineEightFour' hS h98).2.1 hL hLn (hA7 hS p P M H Q K hd L hL) (hBHM hb)
    (TenThreeThree.odd_orderOf_of_isPGroup hesc.prime hesc.ne_two hB hb)
    (fun x hx => hBJ b hb x hx)

theorem agl81TenThreeThreeCasesCfg_of_three (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hNX : NoXBlockFor G) (h98 : AGL81NineEightFour G) (hKT : TenThreeThree.KFactTransvectionW3)
    (hAlt : TenThreeThree.Asc81bAltBlockAutNX) (hA7 : AGL81TenNineOneCfg G)
    (hZ : AGL81TenOneSixCenterCfg G) : AGL81TenThreeThreeCasesCfg G := by
  intro hS p P M H Q K hd L hL hLn b hb hbo hbJ
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hLM : L ≤ M := hL.le
  have hNS : normalizer (pCoreOf 2 H : Set G) ⊓ L = H ⊓ L := by rw [hNH]
  have hPY : barM M (H ⊓ L) ≤ barM M L := map_mono fun x hx => by
    rw [mem_subgroupOf] at hx ⊢
    exact hx.2
  have hX : ¬ InClassXBlock L := (hT.nineThree_not_one hK h85 hNX hL).1
  have hrk := TenThreeThree.pRank_three_barM_le hS hT.maxTwoLocal_M.1 L
  rcases hT.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  ·
    refine Or.inr ⟨h2.1, ?_⟩
    have := h2.2.1
    rwa [hNS] at this
  ·
    have hSy := hT.not_isSylowTwoOf_inf hK h85 hNX hL
    obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ :=
      CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds G M
        (pCoreOf 2 H) L hK hA hL hX hSy h3
    have hPP : barM M (H ⊓ L) = blockPL M (pCoreOf 2 H) L := by rw [blockPL, hNS]
    set eP := MulEquiv.subgroupCongr hPP
    have tr : ∀ {T : Type} [Group T], Nonempty (↥(blockPL M (pCoreOf 2 H) L) ≃* T) →
        Nonempty (↥(barM M (H ⊓ L)) ≃* T) := fun ⟨e⟩ => ⟨eP.trans e⟩
    have trq : ∀ {T : Type} [Group T], Nonempty (↥(blockPL M (pCoreOf 2 H) L) ⧸
        CFSG.pCore 2 ↥(blockPL M (pCoreOf 2 H) L) ≃* T) →
        Nonempty (↥(barM M (H ⊓ L)) ⧸ CFSG.pCore 2 ↥(barM M (H ⊓ L)) ≃* T) := by
      rintro T _ ⟨e⟩
      obtain ⟨e'⟩ := nonempty_quotient_pCore_mulEquiv eP
      exact ⟨e'.trans e⟩
    obtain ⟨hbbo, hbLbar, hbP, hW⟩ := TenThreeThree.bar_action hLM hLn hb hbo hbJ
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases hd with hd | hd | ⟨rfl, hd⟩
      · obtain ⟨d', hd', hP⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
        exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inl ⟨m, d, d', ⟨q, hq, Or.inl hd⟩, hd', ⟨e⟩, trq hP⟩) _ hbbo hbLbar
            hbP hW))
      · obtain ⟨d', hd', hP⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
        exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inl ⟨m, d, d', ⟨q, hq, Or.inr hd⟩, hd', ⟨e⟩, trq hP⟩) _ hbbo hbLbar
            hbP hW))
      · exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inr (Or.inl ⟨Or.inl ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩,
            tr (hU4 d ⟨q, hq, hd⟩ ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
    · rcases hn with rfl | rfl | rfl
      · exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inr (Or.inr ⟨⟨e⟩, tr (hA5 ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
      ·
        obtain ⟨e4⟩ := tr (hA6 ⟨e⟩)
        have hcen := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
          (by norm_num : 4 ≤ 6) e
        refine Or.inr ⟨TenThreeThree.isClassicalTwoOrG2_of_altSix
          (((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans e),
          TenThreeThree.isParabolicTwo_altSix hPY e e4⟩
      · exact Or.inl (TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2
          (hKT _ _ _ hPY hrk (Or.inr (Or.inl ⟨Or.inr ⟨e⟩, tr (hA8 ⟨e⟩)⟩)) _ hbbo hbLbar hbP hW))
  ·
    have hZP := hZ hS p P M H Q K hd L hL h4
    obtain ⟨-, hZc, hA6, -, hS4⟩ := h4
    rw [hNS] at hS4
    exact Or.inr ⟨TenThreeThree.isClassicalTwoOrG2_of_altSix hA6.some,
      TenThreeThree.isParabolicTwo_threeASix hPY hZc hA6 hS4 hZP⟩
  · exact ((hA7 hS p P M H Q K hd L hL).false h5.2.1.some).elim
  all_goals
    left
    obtain ⟨-, hbL, -, hW⟩ := TenThreeThree.bar_action hLM hLn hb hbo hbJ
    have hbS : b ∈ normalizer (pCoreOf 2 H : Set G) := by rw [hNH]; exact hb.1
    have hbLn : b ∈ normalizer (L : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hLM).mp hLn hb.2
    refine TenThreeThree.commutator_mem_pCoreOf_of_centralizes hLM hb.2 ?_
  · exact hAlt G M (pCoreOf 2 H) L hK hA hL hX (Or.inl h6) (H ⊓ L) hNS b hb.2 hbS hbo hbLn hW
  · exact hAlt G M (pCoreOf 2 H) L hK hA hL hX (Or.inr (Or.inl h7)) (H ⊓ L) hNS b hb.2 hbS hbo
      hbLn hW
  · exact hAlt G M (pCoreOf 2 H) L hK hA hL hX (Or.inr (Or.inr h8)) (H ⊓ L) hNS b hb.2 hbS hbo
      hbLn hW

end CFSG.LocalAnalysis.RankThreeTheoremC
